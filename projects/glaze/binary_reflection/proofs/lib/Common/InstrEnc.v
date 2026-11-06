(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition e_bool (b : bool) : Z := if b then 1%Z else 0%Z.
Definition d_bool (z : Z) : bool := Z.eqb z 1%Z.
Lemma d_e_bool (b : bool) : d_bool (e_bool b) = b.
Proof. destruct b; reflexivity. Qed.

Definition e_aluop (x : aluop) : Z :=
  match x with ALU_ADD => 0%Z | ALU_SUB => 1%Z | ALU_SLL => 2%Z | ALU_SLT => 3%Z | ALU_SLTU => 4%Z | ALU_XOR => 5%Z | ALU_SRL => 6%Z | ALU_SRA => 7%Z | ALU_OR => 8%Z | ALU_AND => 9%Z end.
Definition d_aluop (z : Z) : aluop :=
  nth (Z.to_nat z) (ALU_ADD :: ALU_SUB :: ALU_SLL :: ALU_SLT :: ALU_SLTU :: ALU_XOR :: ALU_SRL :: ALU_SRA :: ALU_OR :: ALU_AND :: nil) ALU_ADD.
Lemma d_e_aluop (x : aluop) : d_aluop (e_aluop x) = x.
Proof. destruct x; reflexivity. Qed.

Definition e_amoop (x : amoop) : Z :=
  match x with AMO_SWAP => 0%Z | AMO_ADD => 1%Z | AMO_XOR => 2%Z | AMO_AND => 3%Z | AMO_OR => 4%Z | AMO_MIN => 5%Z | AMO_MAX => 6%Z | AMO_MINU => 7%Z | AMO_MAXU => 8%Z end.
Definition d_amoop (z : Z) : amoop :=
  nth (Z.to_nat z) (AMO_SWAP :: AMO_ADD :: AMO_XOR :: AMO_AND :: AMO_OR :: AMO_MIN :: AMO_MAX :: AMO_MINU :: AMO_MAXU :: nil) AMO_SWAP.
Lemma d_e_amoop (x : amoop) : d_amoop (e_amoop x) = x.
Proof. destruct x; reflexivity. Qed.

Definition e_awidth (x : awidth) : Z :=
  match x with AW => 0%Z | AD => 1%Z end.
Definition d_awidth (z : Z) : awidth :=
  nth (Z.to_nat z) (AW :: AD :: nil) AW.
Lemma d_e_awidth (x : awidth) : d_awidth (e_awidth x) = x.
Proof. destruct x; reflexivity. Qed.

Definition e_branch_cond (x : branch_cond) : Z :=
  match x with BC_EQ => 0%Z | BC_NE => 1%Z | BC_LT => 2%Z | BC_GE => 3%Z | BC_LTU => 4%Z | BC_GEU => 5%Z end.
Definition d_branch_cond (z : Z) : branch_cond :=
  nth (Z.to_nat z) (BC_EQ :: BC_NE :: BC_LT :: BC_GE :: BC_LTU :: BC_GEU :: nil) BC_EQ.
Lemma d_e_branch_cond (x : branch_cond) : d_branch_cond (e_branch_cond x) = x.
Proof. destruct x; reflexivity. Qed.

Definition e_csrop (x : csrop) : Z :=
  match x with CSR_RW => 0%Z | CSR_RS => 1%Z | CSR_RC => 2%Z end.
Definition d_csrop (z : Z) : csrop :=
  nth (Z.to_nat z) (CSR_RW :: CSR_RS :: CSR_RC :: nil) CSR_RW.
Lemma d_e_csrop (x : csrop) : d_csrop (e_csrop x) = x.
Proof. destruct x; reflexivity. Qed.

Definition e_fariop (x : fariop) : Z :=
  match x with F_ADD => 0%Z | F_SUB => 1%Z | F_MUL => 2%Z | F_DIV => 3%Z end.
Definition d_fariop (z : Z) : fariop :=
  nth (Z.to_nat z) (F_ADD :: F_SUB :: F_MUL :: F_DIV :: nil) F_ADD.
Lemma d_e_fariop (x : fariop) : d_fariop (e_fariop x) = x.
Proof. destruct x; reflexivity. Qed.

Definition e_fcmpop (x : fcmpop) : Z :=
  match x with F_EQ => 0%Z | F_LT => 1%Z | F_LE => 2%Z end.
Definition d_fcmpop (z : Z) : fcmpop :=
  nth (Z.to_nat z) (F_EQ :: F_LT :: F_LE :: nil) F_EQ.
Lemma d_e_fcmpop (x : fcmpop) : d_fcmpop (e_fcmpop x) = x.
Proof. destruct x; reflexivity. Qed.

Definition e_fcvt_ty (x : fcvt_ty) : Z :=
  match x with FC_W => 0%Z | FC_WU => 1%Z | FC_L => 2%Z | FC_LU => 3%Z | FC_S => 4%Z | FC_D => 5%Z end.
Definition d_fcvt_ty (z : Z) : fcvt_ty :=
  nth (Z.to_nat z) (FC_W :: FC_WU :: FC_L :: FC_LU :: FC_S :: FC_D :: nil) FC_W.
Lemma d_e_fcvt_ty (x : fcvt_ty) : d_fcvt_ty (e_fcvt_ty x) = x.
Proof. destruct x; reflexivity. Qed.

Definition e_ffmt (x : ffmt) : Z :=
  match x with FMT_S => 0%Z | FMT_D => 1%Z end.
Definition d_ffmt (z : Z) : ffmt :=
  nth (Z.to_nat z) (FMT_S :: FMT_D :: nil) FMT_S.
Lemma d_e_ffmt (x : ffmt) : d_ffmt (e_ffmt x) = x.
Proof. destruct x; reflexivity. Qed.

Definition e_fmaop (x : fmaop) : Z :=
  match x with F_MADD => 0%Z | F_MSUB => 1%Z | F_NMSUB => 2%Z | F_NMADD => 3%Z end.
Definition d_fmaop (z : Z) : fmaop :=
  nth (Z.to_nat z) (F_MADD :: F_MSUB :: F_NMSUB :: F_NMADD :: nil) F_MADD.
Lemma d_e_fmaop (x : fmaop) : d_fmaop (e_fmaop x) = x.
Proof. destruct x; reflexivity. Qed.

Definition e_fminmaxop (x : fminmaxop) : Z :=
  match x with F_MIN => 0%Z | F_MAX => 1%Z end.
Definition d_fminmaxop (z : Z) : fminmaxop :=
  nth (Z.to_nat z) (F_MIN :: F_MAX :: nil) F_MIN.
Lemma d_e_fminmaxop (x : fminmaxop) : d_fminmaxop (e_fminmaxop x) = x.
Proof. destruct x; reflexivity. Qed.

Definition e_fmvdir (x : fmvdir) : Z :=
  match x with FMV_X_F => 0%Z | FMV_F_X => 1%Z end.
Definition d_fmvdir (z : Z) : fmvdir :=
  nth (Z.to_nat z) (FMV_X_F :: FMV_F_X :: nil) FMV_X_F.
Lemma d_e_fmvdir (x : fmvdir) : d_fmvdir (e_fmvdir x) = x.
Proof. destruct x; reflexivity. Qed.

Definition e_fsgnop (x : fsgnop) : Z :=
  match x with F_SGNJ => 0%Z | F_SGNJN => 1%Z | F_SGNJX => 2%Z end.
Definition d_fsgnop (z : Z) : fsgnop :=
  nth (Z.to_nat z) (F_SGNJ :: F_SGNJN :: F_SGNJX :: nil) F_SGNJ.
Lemma d_e_fsgnop (x : fsgnop) : d_fsgnop (e_fsgnop x) = x.
Proof. destruct x; reflexivity. Qed.

Definition e_msize (x : msize) : Z :=
  match x with SZ1 => 0%Z | SZ2 => 1%Z | SZ4 => 2%Z | SZ8 => 3%Z end.
Definition d_msize (z : Z) : msize :=
  nth (Z.to_nat z) (SZ1 :: SZ2 :: SZ4 :: SZ8 :: nil) SZ1.
Lemma d_e_msize (x : msize) : d_msize (e_msize x) = x.
Proof. destruct x; reflexivity. Qed.

Definition e_mulop (x : mulop) : Z :=
  match x with M_MUL => 0%Z | M_MULH => 1%Z | M_MULHSU => 2%Z | M_MULHU => 3%Z | M_DIV => 4%Z | M_DIVU => 5%Z | M_REM => 6%Z | M_REMU => 7%Z end.
Definition d_mulop (z : Z) : mulop :=
  nth (Z.to_nat z) (M_MUL :: M_MULH :: M_MULHSU :: M_MULHU :: M_DIV :: M_DIVU :: M_REM :: M_REMU :: nil) M_MUL.
Lemma d_e_mulop (x : mulop) : d_mulop (e_mulop x) = x.
Proof. destruct x; reflexivity. Qed.

Definition enc (i : instr) : list Z :=
  match i with
  | Lui rd imm => 0%Z :: bv_unsigned rd :: bv_unsigned imm :: nil
  | Auipc rd imm => 1%Z :: bv_unsigned rd :: bv_unsigned imm :: nil
  | Jal rd imm => 2%Z :: bv_unsigned rd :: bv_unsigned imm :: nil
  | Jalr rd rs1 imm => 3%Z :: bv_unsigned rd :: bv_unsigned rs1 :: bv_unsigned imm :: nil
  | Branch c rs1 rs2 imm => 4%Z :: e_branch_cond c :: bv_unsigned rs1 :: bv_unsigned rs2 :: bv_unsigned imm :: nil
  | Load sz signed rd rs1 imm => 5%Z :: e_msize sz :: e_bool signed :: bv_unsigned rd :: bv_unsigned rs1 :: bv_unsigned imm :: nil
  | Store sz rs1 rs2 imm => 6%Z :: e_msize sz :: bv_unsigned rs1 :: bv_unsigned rs2 :: bv_unsigned imm :: nil
  | OpImm op rd rs1 imm => 7%Z :: e_aluop op :: bv_unsigned rd :: bv_unsigned rs1 :: bv_unsigned imm :: nil
  | ShiftImm op rd rs1 shamt => 8%Z :: e_aluop op :: bv_unsigned rd :: bv_unsigned rs1 :: bv_unsigned shamt :: nil
  | Op op rd rs1 rs2 => 9%Z :: e_aluop op :: bv_unsigned rd :: bv_unsigned rs1 :: bv_unsigned rs2 :: nil
  | OpImm32 rd rs1 imm => 10%Z :: bv_unsigned rd :: bv_unsigned rs1 :: bv_unsigned imm :: nil
  | ShiftImm32 op rd rs1 shamt => 11%Z :: e_aluop op :: bv_unsigned rd :: bv_unsigned rs1 :: bv_unsigned shamt :: nil
  | Op32 op rd rs1 rs2 => 12%Z :: e_aluop op :: bv_unsigned rd :: bv_unsigned rs1 :: bv_unsigned rs2 :: nil
  | Fence fm pred succ rd rs1 => 13%Z :: bv_unsigned fm :: bv_unsigned pred :: bv_unsigned succ :: bv_unsigned rd :: bv_unsigned rs1 :: nil
  | FenceI rd rs1 imm => 14%Z :: bv_unsigned rd :: bv_unsigned rs1 :: bv_unsigned imm :: nil
  | Ecall => 15%Z :: nil
  | Ebreak => 16%Z :: nil
  | Mul op rd rs1 rs2 => 17%Z :: e_mulop op :: bv_unsigned rd :: bv_unsigned rs1 :: bv_unsigned rs2 :: nil
  | Mul32 op rd rs1 rs2 => 18%Z :: e_mulop op :: bv_unsigned rd :: bv_unsigned rs1 :: bv_unsigned rs2 :: nil
  | Lr w aq rl rd rs1 => 19%Z :: e_awidth w :: e_bool aq :: e_bool rl :: bv_unsigned rd :: bv_unsigned rs1 :: nil
  | Sc w aq rl rd rs1 rs2 => 20%Z :: e_awidth w :: e_bool aq :: e_bool rl :: bv_unsigned rd :: bv_unsigned rs1 :: bv_unsigned rs2 :: nil
  | Amo op w aq rl rd rs1 rs2 => 21%Z :: e_amoop op :: e_awidth w :: e_bool aq :: e_bool rl :: bv_unsigned rd :: bv_unsigned rs1 :: bv_unsigned rs2 :: nil
  | Csr op rd rs1 csr => 22%Z :: e_csrop op :: bv_unsigned rd :: bv_unsigned rs1 :: bv_unsigned csr :: nil
  | CsrI op rd uimm csr => 23%Z :: e_csrop op :: bv_unsigned rd :: bv_unsigned uimm :: bv_unsigned csr :: nil
  | FLoad fmt rd rs1 imm => 24%Z :: e_ffmt fmt :: bv_unsigned rd :: bv_unsigned rs1 :: bv_unsigned imm :: nil
  | FStore fmt rs1 rs2 imm => 25%Z :: e_ffmt fmt :: bv_unsigned rs1 :: bv_unsigned rs2 :: bv_unsigned imm :: nil
  | Fma op fmt rd rs1 rs2 rs3 rm => 26%Z :: e_fmaop op :: e_ffmt fmt :: bv_unsigned rd :: bv_unsigned rs1 :: bv_unsigned rs2 :: bv_unsigned rs3 :: bv_unsigned rm :: nil
  | Fari op fmt rd rs1 rs2 rm => 27%Z :: e_fariop op :: e_ffmt fmt :: bv_unsigned rd :: bv_unsigned rs1 :: bv_unsigned rs2 :: bv_unsigned rm :: nil
  | Fsqrt fmt rd rs1 rm => 28%Z :: e_ffmt fmt :: bv_unsigned rd :: bv_unsigned rs1 :: bv_unsigned rm :: nil
  | Fsgnj op fmt rd rs1 rs2 => 29%Z :: e_fsgnop op :: e_ffmt fmt :: bv_unsigned rd :: bv_unsigned rs1 :: bv_unsigned rs2 :: nil
  | Fminmax op fmt rd rs1 rs2 => 30%Z :: e_fminmaxop op :: e_ffmt fmt :: bv_unsigned rd :: bv_unsigned rs1 :: bv_unsigned rs2 :: nil
  | Fcmp op fmt rd rs1 rs2 => 31%Z :: e_fcmpop op :: e_ffmt fmt :: bv_unsigned rd :: bv_unsigned rs1 :: bv_unsigned rs2 :: nil
  | Fcvt dst src rd rs1 rm => 32%Z :: e_fcvt_ty dst :: e_fcvt_ty src :: bv_unsigned rd :: bv_unsigned rs1 :: bv_unsigned rm :: nil
  | Fmv dir fmt rd rs1 => 33%Z :: e_fmvdir dir :: e_ffmt fmt :: bv_unsigned rd :: bv_unsigned rs1 :: nil
  | Fclass fmt rd rs1 => 34%Z :: e_ffmt fmt :: bv_unsigned rd :: bv_unsigned rs1 :: nil
  end.

Definition gz (r : list Z) (k : nat) : Z := nth k r 0%Z.
Definition dec_tab : list (list Z -> instr) :=
  (fun r : list Z => Lui (Z_to_bv 5 (gz r 0)) (Z_to_bv 20 (gz r 1))) ::
  (fun r : list Z => Auipc (Z_to_bv 5 (gz r 0)) (Z_to_bv 20 (gz r 1))) ::
  (fun r : list Z => Jal (Z_to_bv 5 (gz r 0)) (Z_to_bv 21 (gz r 1))) ::
  (fun r : list Z => Jalr (Z_to_bv 5 (gz r 0)) (Z_to_bv 5 (gz r 1)) (Z_to_bv 12 (gz r 2))) ::
  (fun r : list Z => Branch (d_branch_cond (gz r 0)) (Z_to_bv 5 (gz r 1)) (Z_to_bv 5 (gz r 2)) (Z_to_bv 13 (gz r 3))) ::
  (fun r : list Z => Load (d_msize (gz r 0)) (d_bool (gz r 1)) (Z_to_bv 5 (gz r 2)) (Z_to_bv 5 (gz r 3)) (Z_to_bv 12 (gz r 4))) ::
  (fun r : list Z => Store (d_msize (gz r 0)) (Z_to_bv 5 (gz r 1)) (Z_to_bv 5 (gz r 2)) (Z_to_bv 12 (gz r 3))) ::
  (fun r : list Z => OpImm (d_aluop (gz r 0)) (Z_to_bv 5 (gz r 1)) (Z_to_bv 5 (gz r 2)) (Z_to_bv 12 (gz r 3))) ::
  (fun r : list Z => ShiftImm (d_aluop (gz r 0)) (Z_to_bv 5 (gz r 1)) (Z_to_bv 5 (gz r 2)) (Z_to_bv 6 (gz r 3))) ::
  (fun r : list Z => Op (d_aluop (gz r 0)) (Z_to_bv 5 (gz r 1)) (Z_to_bv 5 (gz r 2)) (Z_to_bv 5 (gz r 3))) ::
  (fun r : list Z => OpImm32 (Z_to_bv 5 (gz r 0)) (Z_to_bv 5 (gz r 1)) (Z_to_bv 12 (gz r 2))) ::
  (fun r : list Z => ShiftImm32 (d_aluop (gz r 0)) (Z_to_bv 5 (gz r 1)) (Z_to_bv 5 (gz r 2)) (Z_to_bv 5 (gz r 3))) ::
  (fun r : list Z => Op32 (d_aluop (gz r 0)) (Z_to_bv 5 (gz r 1)) (Z_to_bv 5 (gz r 2)) (Z_to_bv 5 (gz r 3))) ::
  (fun r : list Z => Fence (Z_to_bv 4 (gz r 0)) (Z_to_bv 4 (gz r 1)) (Z_to_bv 4 (gz r 2)) (Z_to_bv 5 (gz r 3)) (Z_to_bv 5 (gz r 4))) ::
  (fun r : list Z => FenceI (Z_to_bv 5 (gz r 0)) (Z_to_bv 5 (gz r 1)) (Z_to_bv 12 (gz r 2))) ::
  (fun r : list Z => Ecall) ::
  (fun r : list Z => Ebreak) ::
  (fun r : list Z => Mul (d_mulop (gz r 0)) (Z_to_bv 5 (gz r 1)) (Z_to_bv 5 (gz r 2)) (Z_to_bv 5 (gz r 3))) ::
  (fun r : list Z => Mul32 (d_mulop (gz r 0)) (Z_to_bv 5 (gz r 1)) (Z_to_bv 5 (gz r 2)) (Z_to_bv 5 (gz r 3))) ::
  (fun r : list Z => Lr (d_awidth (gz r 0)) (d_bool (gz r 1)) (d_bool (gz r 2)) (Z_to_bv 5 (gz r 3)) (Z_to_bv 5 (gz r 4))) ::
  (fun r : list Z => Sc (d_awidth (gz r 0)) (d_bool (gz r 1)) (d_bool (gz r 2)) (Z_to_bv 5 (gz r 3)) (Z_to_bv 5 (gz r 4)) (Z_to_bv 5 (gz r 5))) ::
  (fun r : list Z => Amo (d_amoop (gz r 0)) (d_awidth (gz r 1)) (d_bool (gz r 2)) (d_bool (gz r 3)) (Z_to_bv 5 (gz r 4)) (Z_to_bv 5 (gz r 5)) (Z_to_bv 5 (gz r 6))) ::
  (fun r : list Z => Csr (d_csrop (gz r 0)) (Z_to_bv 5 (gz r 1)) (Z_to_bv 5 (gz r 2)) (Z_to_bv 12 (gz r 3))) ::
  (fun r : list Z => CsrI (d_csrop (gz r 0)) (Z_to_bv 5 (gz r 1)) (Z_to_bv 5 (gz r 2)) (Z_to_bv 12 (gz r 3))) ::
  (fun r : list Z => FLoad (d_ffmt (gz r 0)) (Z_to_bv 5 (gz r 1)) (Z_to_bv 5 (gz r 2)) (Z_to_bv 12 (gz r 3))) ::
  (fun r : list Z => FStore (d_ffmt (gz r 0)) (Z_to_bv 5 (gz r 1)) (Z_to_bv 5 (gz r 2)) (Z_to_bv 12 (gz r 3))) ::
  (fun r : list Z => Fma (d_fmaop (gz r 0)) (d_ffmt (gz r 1)) (Z_to_bv 5 (gz r 2)) (Z_to_bv 5 (gz r 3)) (Z_to_bv 5 (gz r 4)) (Z_to_bv 5 (gz r 5)) (Z_to_bv 3 (gz r 6))) ::
  (fun r : list Z => Fari (d_fariop (gz r 0)) (d_ffmt (gz r 1)) (Z_to_bv 5 (gz r 2)) (Z_to_bv 5 (gz r 3)) (Z_to_bv 5 (gz r 4)) (Z_to_bv 3 (gz r 5))) ::
  (fun r : list Z => Fsqrt (d_ffmt (gz r 0)) (Z_to_bv 5 (gz r 1)) (Z_to_bv 5 (gz r 2)) (Z_to_bv 3 (gz r 3))) ::
  (fun r : list Z => Fsgnj (d_fsgnop (gz r 0)) (d_ffmt (gz r 1)) (Z_to_bv 5 (gz r 2)) (Z_to_bv 5 (gz r 3)) (Z_to_bv 5 (gz r 4))) ::
  (fun r : list Z => Fminmax (d_fminmaxop (gz r 0)) (d_ffmt (gz r 1)) (Z_to_bv 5 (gz r 2)) (Z_to_bv 5 (gz r 3)) (Z_to_bv 5 (gz r 4))) ::
  (fun r : list Z => Fcmp (d_fcmpop (gz r 0)) (d_ffmt (gz r 1)) (Z_to_bv 5 (gz r 2)) (Z_to_bv 5 (gz r 3)) (Z_to_bv 5 (gz r 4))) ::
  (fun r : list Z => Fcvt (d_fcvt_ty (gz r 0)) (d_fcvt_ty (gz r 1)) (Z_to_bv 5 (gz r 2)) (Z_to_bv 5 (gz r 3)) (Z_to_bv 3 (gz r 4))) ::
  (fun r : list Z => Fmv (d_fmvdir (gz r 0)) (d_ffmt (gz r 1)) (Z_to_bv 5 (gz r 2)) (Z_to_bv 5 (gz r 3))) ::
  (fun r : list Z => Fclass (d_ffmt (gz r 0)) (Z_to_bv 5 (gz r 1)) (Z_to_bv 5 (gz r 2))) :: nil.
Definition dec (l : list Z) : instr :=
  match l with nil => Ebreak | t :: r => nth (Z.to_nat t) dec_tab (fun _ : list Z => Ebreak) r end.

Lemma dec_enc (i : instr) : dec (enc i) = i.
Proof.
  destruct i; cbv beta iota delta [dec enc dec_tab gz nth Z.to_nat Pos.to_nat Pos.iter_op Nat.add];
    rewrite ?Z_to_bv_bv_unsigned, ?d_e_bool, ?d_e_aluop, ?d_e_amoop, ?d_e_awidth, ?d_e_branch_cond, ?d_e_csrop, ?d_e_fariop, ?d_e_fcmpop, ?d_e_fcvt_ty, ?d_e_ffmt, ?d_e_fmaop, ?d_e_fminmaxop, ?d_e_fmvdir, ?d_e_fsgnop, ?d_e_msize, ?d_e_mulop; reflexivity.
Qed.

Definition enc_opt (o : option (instr * Z)) : list Z :=
  match o with None => nil | Some (i, k) => k :: enc i end.
Definition dec_opt (l : list Z) : option (instr * Z) :=
  match l with nil => None | k :: r => Some (dec r, k) end.
Lemma dec_enc_opt (o : option (instr * Z)) : dec_opt (enc_opt o) = o.
Proof. destruct o as [[i k]|]; [exact (f_equal (fun j => Some (j, k)) (dec_enc i)) | reflexivity]. Qed.

Lemma enc_opt_inj (a b : option (instr * Z)) : enc_opt a = enc_opt b -> a = b.
Proof. intros H. exact (eq_trans (eq_sym (dec_enc_opt a)) (eq_trans (f_equal dec_opt H) (dec_enc_opt b))). Qed.
