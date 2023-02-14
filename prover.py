from compiler.program import Program, CommonPreprocessedInput
from utils import *
from setup import *
from typing import Optional
from dataclasses import dataclass
from transcript import Transcript, Message1, Message2, Message3, Message4, Message5
from poly import Polynomial, Basis


@dataclass
class Proof:
    msg_1: Message1
    msg_2: Message2
    msg_3: Message3
    msg_4: Message4
    msg_5: Message5

    def flatten(self):
        proof = {}
        proof["a_1"] = self.msg_1.a_1
        proof["b_1"] = self.msg_1.b_1
        proof["c_1"] = self.msg_1.c_1
        proof["z_1"] = self.msg_2.z_1
        proof["t_lo_1"] = self.msg_3.t_lo_1
        proof["t_mid_1"] = self.msg_3.t_mid_1
        proof["t_hi_1"] = self.msg_3.t_hi_1
        proof["a_eval"] = self.msg_4.a_eval
        proof["b_eval"] = self.msg_4.b_eval
        proof["c_eval"] = self.msg_4.c_eval
        proof["s1_eval"] = self.msg_4.s1_eval
        proof["s2_eval"] = self.msg_4.s2_eval
        proof["z_shifted_eval"] = self.msg_4.z_shifted_eval
        proof["W_z_1"] = self.msg_5.W_z_1
        proof["W_zw_1"] = self.msg_5.W_zw_1
        return proof


@dataclass
class Prover:
    group_order: int
    setup: Setup
    program: Program
    pk: CommonPreprocessedInput

    def __init__(self, setup: Setup, program: Program):
        self.group_order = program.group_order
        self.setup = setup
        self.program = program
        self.pk = program.common_preprocessed_input()

    def prove(self, witness: dict[Optional[str], int]) -> Proof:
        # Initialise Fiat-Shamir transcript
        transcript = Transcript(b"plonk")

        # Collect fixed and public information
        # FIXME: Hash pk and PI into transcript
        public_vars = self.program.get_public_assignments()
        PI = Polynomial(
            [Scalar(-witness[v]) for v in public_vars]
            + [Scalar(0) for _ in range(self.group_order - len(public_vars))],
            Basis.LAGRANGE,
        )
        self.PI = PI

        # Round 1
        msg_1 = self.round_1(witness)
        self.beta, self.gamma = transcript.round_1(msg_1)

        # Round 2
        msg_2 = self.round_2()
        self.alpha, self.fft_cofactor = transcript.round_2(msg_2)

        # Round 3
        msg_3 = self.round_3()
        self.zeta = transcript.round_3(msg_3)

        # Round 4
        msg_4 = self.round_4()
        self.v = transcript.round_4(msg_4)

        # Round 5
        msg_5 = self.round_5()

        return Proof(msg_1, msg_2, msg_3, msg_4, msg_5)

    def round_1(
        self,
        witness: dict[Optional[str], int],
    ) -> Message1:
        program = self.program
        setup = self.setup
        group_order = self.group_order

        if None not in witness:
            witness[None] = 0

        # Compute wire assignments for A, B, C, corresponding:
        # - A_values: witness[program.wires()[i].L]
        # - B_values: witness[program.wires()[i].R]
        # - C_values: witness[program.wires()[i].O]
        print ("witness", witness)

        A_values = [Scalar(0)]*group_order
        B_values = [Scalar(0)]*group_order
        C_values = [Scalar(0)]*group_order

        for i in range(len(program.wires())):
            A_values[i] = Scalar(witness[program.wires()[i].L])
            B_values[i] = Scalar(witness[program.wires()[i].R])
            C_values[i] = Scalar(witness[program.wires()[i].O])

        print("A_values", A_values)
        print("program pk", self.pk.QM.values)
        print("basis", self.pk.QM.basis)

        # Construct A, B, C Lagrange interpolation polynomials for
        # A_values, B_values, C_values
        self.A = Polynomial(A_values, Basis.LAGRANGE)
        self.B = Polynomial(B_values, Basis.LAGRANGE)
        self.C = Polynomial(C_values, Basis.LAGRANGE)

        print("A", self.A.values)

        # Compute A, B, C evaluations at roots of unity
        roots_of_unity = Scalar.roots_of_unity(group_order)
        print("roots_of_unity", roots_of_unity)
        eval_a = self.A.barycentric_eval(Scalar(1))
        print(eval_a)
        eval_a2 = self.A.barycentric_eval(roots_of_unity[1])
        print(eval_a2)
        eval_a3 = self.A.barycentric_eval(roots_of_unity[6])
        print(eval_a3)
        

        # Compute a_1, b_1, c_1 commitments to A, B, C polynomials
        a_1 = setup.commit(self.A)
        b_1 = setup.commit(self.B)
        c_1 = setup.commit(self.C)

        # Sanity check that witness fulfils gate constraints
        assert (
            self.A * self.pk.QL
            + self.B * self.pk.QR
            + self.A * self.B * self.pk.QM
            + self.C * self.pk.QO
            + self.PI
            + self.pk.QC
            == Polynomial([Scalar(0)] * group_order, Basis.LAGRANGE)
        )

        # Return a_1, b_1, c_1
        return Message1(a_1, b_1, c_1)

    def round_2(self) -> Message2:
        group_order = self.group_order
        setup = self.setup

        # Using A, B, C, values, and pk.S1, pk.S2, pk.S3, compute
        # Z_values for permutation grand product polynomial Z
        #
        # Note the convenience function:
        #       self.rlc(val1, val2) = val_1 + self.beta * val_2 + gamma

        # Compute Z_values
        roots_of_unity = Scalar.roots_of_unity(group_order)

        Z_values = [Scalar(1)]
        for i in range(group_order):
             #fprime = self.rlc(A(roots_of_unity[i]), i)
            Z_values.append(Z_values[-1]
            * self.rlc(self.A.values[i], roots_of_unity[i])
            * self.rlc(self.B.values[i], 2 * roots_of_unity[i])
            * self.rlc(self.C.values[i], 3 * roots_of_unity[i])
            / self.rlc(self.A.values[i], self.pk.S1.values[i])
            / self.rlc(self.B.values[i], self.pk.S2.values[i])
            / self.rlc(self.C.values[i], self.pk.S3.values[i])
            ) 

        # fprime(g_i) = f(g_i) + B*i + gamma
       
               
        #for i in range(1, group_order):
        #    Z_values[i] = Z_values[i-1] 
        #    Z_values[i] = Z_values[i-1] * self.rlc(self.A.values[i], roots_of_unity[i]) * self.rlc(self.B.values[i], 2 * roots_of_unity[i]) * self.rlc(self.C.values[i], 3 * roots_of_unity[i])/ self.rlc(self.A.values[i], self.pk.S1.values[i]) / self.rlc(self.B.values[i], self.pk.S2.values[i]) / self.rlc(self.C.values[i], self.pk.S3.values[i])



        print("Z_values", Z_values)


        # Check that the last term Z_n = 1
        assert Z_values.pop() == 1

        # Sanity-check that Z was computed correctly
        for i in range(group_order):
            assert (
                self.rlc(self.A.values[i], roots_of_unity[i])
                * self.rlc(self.B.values[i], 2 * roots_of_unity[i])
                * self.rlc(self.C.values[i], 3 * roots_of_unity[i])
            ) * Z_values[i] - (
                self.rlc(self.A.values[i], self.pk.S1.values[i])
                * self.rlc(self.B.values[i], self.pk.S2.values[i])
                * self.rlc(self.C.values[i], self.pk.S3.values[i])
            ) * Z_values[
                (i + 1) % group_order
            ] == 0

        # Construct Z, Lagrange interpolation polynomial for Z_values
        # Cpmpute z_1 commitment to Z polynomial

        self.Z = Polynomial(Z_values, Basis.LAGRANGE)
        z_1 = setup.commit(self.Z)

        # Return z_1
        return Message2(z_1)

    def round_3(self) -> Message3:
        group_order = self.group_order
        setup = self.setup

        # Compute the quotient polynomial

        # List of roots of unity at 4x fineness, i.e. the powers of µ
        # where µ^(4n) = 1

        roots_of_unity_4n = Scalar.roots_of_unity(group_order * 4)
        print("roots_of_unity_4", roots_of_unity_4n)
        assert len(roots_of_unity_4n) == group_order * 4
        
        # Using self.fft_expand, move A, B, C into coset extended Lagrange basis
        
        self.A_big = self.fft_expand(self.A)
        self.B_big = self.fft_expand(self.B)
        self.C_big = self.fft_expand(self.C)

        # Expand public inputs polynomial PI into coset extended Lagrange

        self.PI_big = self.fft_expand(self.PI)

        # Expand selector polynomials pk.QL, pk.QR, pk.QM, pk.QO, pk.QC
        # into the coset extended Lagrange basis

        self.QL_big = self.fft_expand(self.pk.QL)
        self.QR_big = self.fft_expand(self.pk.QR)
        self.QM_big = self.fft_expand(self.pk.QM)
        self.QO_big = self.fft_expand(self.pk.QO)
        self.QC_big = self.fft_expand(self.pk.QC)

        # Expand permutation grand product polynomial Z into coset extended
        # Lagrange basis

        self.Z_big = self.fft_expand(self.Z)

        # Expand shifted Z(ω) into coset extended Lagrange basis

        self.Z_omega = self.Z.shift(1)
        self.Z_omega_big = self.fft_expand(self.Z_omega)

        # Expand permutation polynomials pk.S1, pk.S2, pk.S3 into coset
        # extended Lagrange basis

        self.S1_big = self.fft_expand(self.pk.S1)
        self.S2_big = self.fft_expand(self.pk.S2)
        self.S3_big = self.fft_expand(self.pk.S3)

        # Compute Z_H = X^N - 1, also in evaluation form in the coset

        Z_H = Polynomial(
            [Scalar(-1)] + [Scalar(0)] * (group_order - 2) + [Scalar(1)], Basis.MONOMIAL
        ).fft()
        print("Z_H", Z_H.values)
        print ("Z_H eval", Z_H.barycentric_eval(roots_of_unity_4n[1]))
        ZH_big = self.fft_expand(Z_H)
        print("ZH_big", ZH_big.values)

        ZH_big_2 = Polynomial(
            [
                ((Scalar(r)*self.fft_cofactor) ** group_order -1)
                for r in roots_of_unity_4n
            ],
            Basis.LAGRANGE,
        )
        print("ZH_big_2", ZH_big_2.values)
        # transform to normal coefficients
        normal_coefficients = ZH_big_2.coset_extended_lagrange_to_coeffs(self.fft_cofactor)
        print("normal_coefficients", normal_coefficients.values)

        ZH_3 = Polynomial(
            [(Scalar(x)) for x in [21888242871839275222246405745257275088548364400416034343698204186575808495616, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], 
            Basis.MONOMIAL
        )
        print("ZH_3", ZH_3.values)
        ZH_3_big = self.fft_expand(ZH_3.fft())
        print("ZH_3_big", ZH_3_big.values)

        #assert ZH_3_big == ZH_big_2




        # Compute L0, the Lagrange basis polynomial that evaluates to 1 at x = 1 = ω^0
        # and 0 at other roots of unity

        # Expand L0 into the coset extended Lagrange basis
        L0_big = self.fft_expand(
            Polynomial([Scalar(1)] + [Scalar(0)] * (group_order - 1), Basis.LAGRANGE)
        )

        # Compute the quotient polynomial (called T(x) in the paper)
        # It is only possible to construct this polynomial if the following
        # equations are true at all roots of unity {1, w ... w^(n-1)}:
        # 1. All gates are correct:
        #    A * QL + B * QR + A * B * QM + C * QO + PI + QC = 0
        #
        # 2. The permutation accumulator is valid:
        #    Z(wx) = Z(x) * (rlc of A, X, 1) * (rlc of B, 2X, 1) *
        #                   (rlc of C, 3X, 1) / (rlc of A, S1, 1) /
        #                   (rlc of B, S2, 1) / (rlc of C, S3, 1)
        #    rlc = random linear combination: term_1 + beta * term2 + gamma * term3
        #
        # 3. The permutation accumulator equals 1 at the start point
        #    (Z - 1) * L0 = 0
        #    L0 = Lagrange polynomial, equal at all roots of unity except 1

        roots_of_unity_4n_poly = Polynomial(roots_of_unity_4n, Basis.LAGRANGE)
        print("roots_of_unity_4n_poly", roots_of_unity_4n_poly.values)

        # to monomial
        roots_of_unity_4n_poly_mono = roots_of_unity_4n_poly.ifft()
        print("roots_of_unity_4n_poly_mono", roots_of_unity_4n_poly_mono.values)

        x = self.fft_expand(Polynomial([Scalar(0), Scalar(1)]+[Scalar(0)]*(group_order-2), Basis.MONOMIAL).fft())
        print("x", x.values)
        print ("len x", len(x.values))
        print ("len Z_big", len(self.Z_big.values))
        assert len(x.values) == len(self.Z_big.values)
        QUOT_big = (
            self.A_big * self.QL_big
            + self.B_big * self.QR_big
            + self.A_big * self.B_big * self.QM_big
            + self.C_big * self.QO_big
            + self.PI_big
            + self.QC_big
        )+ ((self.rlc(self.A_big,roots_of_unity_4n_poly*self.fft_cofactor)*
            self.rlc(self.B_big,roots_of_unity_4n_poly*(2*self.fft_cofactor))*
            self.rlc(self.C_big,roots_of_unity_4n_poly*(3*self.fft_cofactor))*
            self.Z_big)
            *self.alpha
        ) - (
            self.rlc(self.A_big,self.S1_big)*self.rlc(self.B_big,self.S2_big)*self.rlc(self.C_big,self.S3_big)*self.Z_omega_big*self.alpha
        )+ (
            (self.Z_big - x) * L0_big * self.alpha * self.alpha
        )
        QUOT_big /= ZH_big_2

        print("QUOT_big", QUOT_big.values)
        print("len QUOT_big", len(QUOT_big.values))

        quot_to_coeffs = self.expanded_evals_to_coeffs(QUOT_big)
        print("quot_to_coeffs", quot_to_coeffs.values)
        print("len quot_to_coeffs", len(quot_to_coeffs.values))
        

        # Sanity check: QUOT has degree < 3n
        assert (
            self.expanded_evals_to_coeffs(QUOT_big).values[-group_order:]
            == [0] * group_order
        )
        print("Generated the quotient polynomial")

        # Split up T into T1, T2 and T3 (needed because T has degree 3n - 4, so is
        # too big for the trusted setup)

        T1 = Polynomial(quot_to_coeffs.values[:group_order], Basis.MONOMIAL).fft()
        T2 = Polynomial(quot_to_coeffs.values[group_order : 2 * group_order], Basis.MONOMIAL).fft()
        T3 = Polynomial(quot_to_coeffs.values[2 * group_order :], Basis.MONOMIAL).fft()

        fft_cofactor = self.fft_cofactor

        # Sanity check that we've computed T1, T2, T3 correctly
        assert (
            T1.barycentric_eval(fft_cofactor)
            + T2.barycentric_eval(fft_cofactor) * fft_cofactor**group_order
            + T3.barycentric_eval(fft_cofactor) * fft_cofactor ** (group_order * 2)
        ) == QUOT_big.values[0]

        print("Generated T1, T2, T3 polynomials")

        # Compute commitments t_lo_1, t_mid_1, t_hi_1 to T1, T2, T3 polynomials
        t_lo_1 = setup.commit(T1)
        t_mid_1 = setup.commit(T2)
        t_hi_1 = setup.commit(T3)

        # Return t_lo_1, t_mid_1, t_hi_1
        return Message3(t_lo_1, t_mid_1, t_hi_1)

    def round_4(self) -> Message4:
        # Compute evaluations to be used in constructing the linearization polynomial.

        # Compute a_eval = A(zeta)
        # Compute b_eval = B(zeta)
        # Compute c_eval = C(zeta)
        # Compute s1_eval = pk.S1(zeta)
        # Compute s2_eval = pk.S2(zeta)
        # Compute z_shifted_eval = Z(zeta * ω)

        # Return a_eval, b_eval, c_eval, s1_eval, s2_eval, z_shifted_eval
        return Message4(a_eval, b_eval, c_eval, s1_eval, s2_eval, z_shifted_eval)

    def round_5(self) -> Message5:
        # Evaluate the Lagrange basis polynomial L0 at zeta
        # Evaluate the vanishing polynomial Z_H(X) = X^n - 1 at zeta

        # Move T1, T2, T3 into the coset extended Lagrange basis
        # Move pk.QL, pk.QR, pk.QM, pk.QO, pk.QC into the coset extended Lagrange basis
        # Move Z into the coset extended Lagrange basis
        # Move pk.S3 into the coset extended Lagrange basis

        # Compute the "linearization polynomial" R. This is a clever way to avoid
        # needing to provide evaluations of _all_ the polynomials that we are
        # checking an equation betweeen: instead, we can "skip" the first
        # multiplicand in each term. The idea is that we construct a
        # polynomial which is constructed to equal 0 at Z only if the equations
        # that we are checking are correct, and which the verifier can reconstruct
        # the KZG commitment to, and we provide proofs to verify that it actually
        # equals 0 at Z
        #
        # In order for the verifier to be able to reconstruct the commitment to R,
        # it has to be "linear" in the proof items, hence why we can only use each
        # proof item once; any further multiplicands in each term need to be
        # replaced with their evaluations at Z, which do still need to be provided

        # Commit to R

        # Sanity-check R
        assert R.barycentric_eval(zeta) == 0

        print("Generated linearization polynomial R")

        # Generate proof that W(z) = 0 and that the provided evaluations of
        # A, B, C, S1, S2 are correct

        # Move A, B, C into the coset extended Lagrange basis
        # Move pk.S1, pk.S2 into the coset extended Lagrange basis

        # In the COSET EXTENDED LAGRANGE BASIS,
        # Construct W_Z = (
        #     R
        #   + v * (A - a_eval)
        #   + v**2 * (B - b_eval)
        #   + v**3 * (C - c_eval)
        #   + v**4 * (S1 - s1_eval)
        #   + v**5 * (S2 - s2_eval)
        # ) / (X - zeta)

        # Check that degree of W_z is not greater than n
        assert W_z_coeffs[group_order:] == [0] * (group_order * 3)

        # Compute W_z_1 commitment to W_z

        # Generate proof that the provided evaluation of Z(z*w) is correct. This
        # awkwardly different term is needed because the permutation accumulator
        # polynomial Z is the one place where we have to check between adjacent
        # coordinates, and not just within one coordinate.
        # In other words: Compute W_zw = (Z - z_shifted_eval) / (X - zeta * ω)

        # Check that degree of W_z is not greater than n
        assert W_zw_coeffs[group_order:] == [0] * (group_order * 3)

        # Compute W_z_1 commitment to W_z

        print("Generated final quotient witness polynomials")

        # Return W_z_1, W_zw_1
        return Message5(W_z_1, W_zw_1)

    def fft_expand(self, x: Polynomial):
        return x.to_coset_extended_lagrange(self.fft_cofactor)

    def expanded_evals_to_coeffs(self, x: Polynomial):
        return x.coset_extended_lagrange_to_coeffs(self.fft_cofactor)

    def rlc(self, term_1, term_2):
        return term_1 + term_2 * self.beta + self.gamma
