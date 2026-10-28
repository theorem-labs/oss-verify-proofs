From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk MemSplit FPSteps.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptStructs LeptRop LeptExec LeptExecW LeptExecB.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac v23_vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Lemma and3_0 : forall p : Z, (0 <= p < 2 ^ 64)%Z -> (p mod 4 = 0)%Z -> alu64 ALU_AND (Z_to_bv 64 p) (Z_to_bv 64 3) = Z_to_bv 64 0.
Proof.
  intros p Hp Hm. rewrite alu_and. unfold v_and. rewrite !u_Z2bv by lia.
  change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2)%Z with 4%Z. rewrite Hm. reflexivity.
Qed.

Lemma and7_0 : forall p : Z, (0 <= p < 2 ^ 64)%Z -> (p mod 8 = 0)%Z -> alu64 ALU_AND (Z_to_bv 64 p) (Z_to_bv 64 7) = Z_to_bv 64 0.
Proof.
  intros p Hp Hm. rewrite alu_and. unfold v_and. rewrite !u_Z2bv by lia.
  change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3)%Z with 8%Z. rewrite Hm. reflexivity.
Qed.

Lemma mod16_to4 : forall a : Z, (a mod 16 = 0)%Z -> (a mod 4 = 0)%Z.
Proof.
  intros a H. apply Z.mod_divide; [lia|]. apply Z.mod_divide in H; [|lia].
  apply (Z.divide_trans 4 16 a); [exists 4%Z; reflexivity | exact H].
Qed.

Lemma mod16_to8 : forall a : Z, (a mod 16 = 0)%Z -> (a mod 8 = 0)%Z.
Proof.
  intros a H. apply Z.mod_divide; [lia|]. apply Z.mod_divide in H; [|lia].
  apply (Z.divide_trans 8 16 a); [exists 2%Z; reflexivity | exact H].
Qed.

Lemma mod8_to4 : forall a : Z, (a mod 8 = 0)%Z -> (a mod 4 = 0)%Z.
Proof.
  intros a H. apply Z.mod_divide; [lia|]. apply Z.mod_divide in H; [|lia].
  apply (Z.divide_trans 4 8 a); [exists 2%Z; reflexivity | exact H].
Qed.

Lemma mod0_add : forall a c k : Z, (0 < k)%Z -> (a mod k = 0)%Z -> (c mod k = 0)%Z -> ((a + c) mod k = 0)%Z.
Proof. intros a c k Hk Ha Hc. rewrite Z.add_mod by lia. rewrite Ha, Hc. apply Z.mod_0_l. lia. Qed.

Lemma mod0_sub : forall a c k : Z, (0 < k)%Z -> (a mod k = 0)%Z -> (c mod k = 0)%Z -> ((a - c) mod k = 0)%Z.
Proof. intros a c k Hk Ha Hc. rewrite Zminus_mod. rewrite Ha, Hc. change (0 - 0)%Z with 0%Z. apply Z.mod_0_l. lia. Qed.

Lemma mod_mul_l : forall k b : Z, (0 < k)%Z -> ((k * b) mod k = 0)%Z.
Proof. intros k b Hk. rewrite Z.mul_comm. apply Z.mod_mul. lia. Qed.

Ltac modz_base :=
  first [ assumption | (apply mod16_to4; assumption) | (apply mod16_to8; assumption) | (apply mod8_to4; assumption)
        | reflexivity | (apply mod_mul_l; lia) ].
Ltac modz :=
  first [ modz_base
        | (apply mod0_add; [lia | modz | modz])
        | (apply mod0_sub; [lia | modz | modz]) ].

Lemma nzi_eq : forall p q : Z, (1 <= p < 2 ^ 64)%Z -> (1 <= q < 2 ^ 64)%Z ->
  branch_taken BC_EQ (alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 p)) (alu64 ALU_SLTU (Z_to_bv 64 q) (Z_to_bv 64 1)) = false.
Proof.
  intros p q Hp Hq. rewrite !alu_sltu, !WalksLib.v_sltu_Z by lia.
  rewrite (proj2 (Z.ltb_lt 0 p)) by lia. rewrite (proj2 (Z.ltb_ge q 1)) by lia. vm_compute. reflexivity.
Qed.

Lemma nzi_xor : forall p q : Z, (1 <= p < 2 ^ 64)%Z -> (1 <= q < 2 ^ 64)%Z ->
  branch_taken BC_EQ (alu64 ALU_XOR (alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 p)) (alu64 ALU_SLTU (Z_to_bv 64 q) (Z_to_bv 64 1))) (Z_to_bv 64 0) = false.
Proof.
  intros p q Hp Hq. rewrite !alu_sltu, !WalksLib.v_sltu_Z by lia.
  rewrite (proj2 (Z.ltb_lt 0 p)) by lia. rewrite (proj2 (Z.ltb_ge q 1)) by lia. vm_compute. reflexivity.
Qed.

Lemma sltu1_nz : forall p : Z, (1 <= p < 2 ^ 64)%Z -> alu64 ALU_SLTU (Z_to_bv 64 p) (Z_to_bv 64 1) = Z_to_bv 64 0.
Proof. intros p Hp. rewrite alu_sltu, WalksLib.v_sltu_Z by lia. rewrite (proj2 (Z.ltb_ge p 1)) by lia. reflexivity. Qed.

Lemma sltu0_nz : forall p : Z, (1 <= p < 2 ^ 64)%Z -> alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 p) = Z_to_bv 64 1.
Proof. intros p Hp. rewrite alu_sltu, WalksLib.v_sltu_Z by lia. rewrite (proj2 (Z.ltb_lt 0 p)) by lia. reflexivity. Qed.

Ltac v23_and0 :=
  repeat match goal with
  | |- context [alu64 ALU_AND (Z_to_bv 64 ?p) (Z_to_bv 64 3)] => rewrite (and3_0 p) by (first [lia | modz])
  | |- context [alu64 ALU_AND (Z_to_bv 64 ?p) (Z_to_bv 64 7)] => rewrite (and7_0 p) by (first [lia | modz])
  | |- context [alu64 ALU_SLTU (Z_to_bv 64 ?p) (Z_to_bv 64 1)] => rewrite (sltu1_nz p) by lia
  | |- context [alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 ?p)] => rewrite (sltu0_nz p) by lia
  end.

Lemma v23_ne_f : forall a b : Z, a = b -> branch_taken BC_NE (Z_to_bv 64 a) (Z_to_bv 64 b) = false.
Proof.
  intros a b ->. cbn [branch_taken]. unfold bv_eqb.
  first [ rewrite Z.eqb_refl; reflexivity | apply negb_false_iff; apply Z.eqb_eq; reflexivity ].
Qed.

Lemma v23_eq_t : forall a b : Z, a = b -> branch_taken BC_EQ (Z_to_bv 64 a) (Z_to_bv 64 b) = true.
Proof.
  intros a b ->. cbn [branch_taken]. unfold bv_eqb.
  first [ rewrite Z.eqb_refl; reflexivity | apply Z.eqb_eq; reflexivity ].
Qed.

Ltac v23_norm :=
  repeat first [ rewrite ex_sx32 by lia | rewrite w_subw | rewrite w_addw | rewrite m_mul | rewrite zbv_mul
               | rewrite ex_ptr_val | rewrite subw_fit by lia | rewrite addw_fit by lia | rewrite sltu1_nz by lia ].

Ltac v23_sc_hook :=
  first
  [ lazymatch goal with
    | |- branch_taken BC_EQ (alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 ?p)) (alu64 ALU_SLTU (Z_to_bv 64 ?q) (Z_to_bv 64 1)) = false =>
        apply nzi_eq; lia
    | |- branch_taken BC_EQ (alu64 ALU_XOR (alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 ?p)) (alu64 ALU_SLTU (Z_to_bv 64 ?q) (Z_to_bv 64 1))) (Z_to_bv 64 0) = false =>
        apply nzi_xor; lia
    end
  | (v23_and0; lazymatch goal with |- ?G => is_closed_term G end; vm_compute; reflexivity)
  | (v23_norm; first [ (apply v23_ne_f; lia) | (apply v23_eq_t; lia) ]) ].

Ltac dbg_run fuel stops scr HR HK :=
  lazymatch type of HR with regs_ok ?E ?sr ?regs =>
  lazymatch type of HK with know_ok ?segs _ ?base ?kn =>
  lazymatch goal with |- context [mkst regs (Z_to_bv 64 ?pc) base ?rom] =>
    let nx := ex_nx E in
    let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn nx) []) in
    lazymatch r with (?ss', ?scs, ?scr') => let p := eval vm_compute in (s_pc ss') in idtac "DBG pc" p "scs" scs "scr" scr' end
  end end end.

Ltac v23_bytes_eq regs :=
  first [ solve [ f_equal; ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add];
                  repeat match goal with H : getr regs _ = Z_to_bv 64 _ |- _ => rewrite H end;
                  rewrite ?ex_sx32 by lia; rewrite ?ex_ptr_val; first [reflexivity | (f_equal; lia)] ]
        | ex_bytes_eq regs ].
Ltac v23_mem regs Hms :=
  eapply ex_msteps_mem; [exact Hms |];
  cbn [mem_denot s_log e_addr e_width e_val];
  repeat (apply ex_wbytes_eq; [ | ex_addr_eq regs | v23_bytes_eq regs ]);
  reflexivity.
Ltac v23_reg regs HR' :=
  first
  [ lazymatch goal with
    | |- getr _ ?k = _ =>
        rewrite (reg_val _ _ _ k HR');
        match goal with |- context [sr_get ?sr k] => let e := eval vm_compute in (sr_get sr k) in change (sr_get sr k) with e end;
        ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add];
        repeat match goal with H : getr regs _ = _ |- _ => progress rewrite H end;
        v23_norm;
        first [ reflexivity | assumption | (f_equal; lia)
              | (rewrite ?zbv_addw_small by lia; first [reflexivity | (f_equal; lia)])
              | (rewrite ?zbv_add; first [reflexivity | (f_equal; lia)])
              | (rewrite <- ?alu_and, <- ?alu_sltu; v23_and0; lazymatch goal with |- ?G => is_closed_term G end; vm_compute; reflexivity) ]
    end
  | ex_reg regs HR' ].
