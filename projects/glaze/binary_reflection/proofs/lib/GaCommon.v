(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.glaze.binary_reflection.images Require Export Asan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.AzDev. Export OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.AzDev.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Export GlzConst.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.RunLim.
Export ListNotations. Export AX2. Export AX2S. Export AP. Export GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition regs0 : list expr := ELit 0 :: map EVar (seq 0 31).

Definition e_sp : expr := EVar 1.
Definition e_a0 : expr := EVar 9.   Definition e_a1 : expr := EVar 10.
Definition e_a2 : expr := EVar 11.  Definition e_a3 : expr := EVar 12.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition objhi (n : Z) : Z := HI47 - n.
(* [comment removed for export] *)
Definition IMG_LO : Z := 0x10000.
Definition IMG_SZ : Z := 0x64d000.      (* [comment removed for export] *)
Definition img_apart (x : expr) (k : Z) (n : expr) : kentry := KDisj (SA x k) n (SA (ELit 0) IMG_LO) (ELit IMG_SZ).
(* [comment removed for export] *)
Definition shmap_apart (x : expr) (k : Z) (n : expr) : kentry := KDisj (SA x k) n (SA (ELit 0) SHMAPLO) (ELit SHMAPLEN).
(* [comment removed for export] *)
Definition shok (x : expr) (k : Z) (n : Z) : kentry := KShOk (SA x k) (ELit n).



(* [comment removed for export] *)
Definition mkcs (ylo : Z) (ws : list (expr * expr)) (mtr fb : expr) (p : Z) (regs : list expr) (k : list kentry) (nx : nat) : acs :=
  ACS (mk_ss p regs k nx) [] 0 ylo 0 [] ws 0 e_sp FdStd false mtr [] fb.

(* [comment removed for export] *)
Definition caller_saved_but_a01 : list nat := [5; 6; 7; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Fixpoint sr_havoc (sr : list expr) (ixs : list nat) (v : nat) : list expr :=
  match ixs with [] => sr | i :: t => sr_havoc (sr_upd sr i (EVar v)) t (S v) end.

(* [comment removed for export] *)
Definition str_L (obj a size data : expr) : list kentry :=
  [ KRange obj PTRLO (objhi 24);
    KWord (SA obj 0) 8 (eaddz (escale 8 a) 1); KWord (SA obj 8) 8 size; KWord (SA obj 16) 8 data ].

(* [comment removed for export] *)
Definition sp_facts (ylo : Z) : list kentry := [KAlign e_sp 16; KRange e_sp (CEIL + ylo) HI47].
(* [comment removed for export] *)
Definition frame_facts (fr : Z) (objs : list (expr * Z)) : list kentry :=
  KWr (SA e_sp (- fr)) (ELit fr) :: map (fun o => KDisj (SA (fst o) 0) (ELit (snd o)) (SA e_sp (- fr)) (ELit fr)) objs.

(* [comment removed for export] *)
Definition RTC_SB : Z := 0x107578.  Definition RTC_UAR : Z := 0x107580.
Definition RTC : list kentry := [KWord (SA (ELit 0) RTC_SB) 8 (ELit SB); KWord (SA (ELit 0) RTC_UAR) 4 (ELit 1)].
(* [comment removed for export] *)
Definition KIMGA_HI : Z := 0x101000.
Definition KIMGA : kentry := KImg (g_ro_lo GASAN) KIMGA_HI.

(* [comment removed for export] *)
Definition GLZ_LO0 : Z := 0x10000.  Definition GLZ_HI0 : Z := 0x22b20.   (* [comment removed for export] *)
Definition GLZ_LO1 : Z := 0x22bc0.  Definition GLZ_HI1 : Z := 0x269a0.
Definition GLZ_LO2 : Z := 0x26b00.  Definition GLZ_HI2 : Z := 0x31340.
Definition GLZ_LOWSH : list kentry :=
  [KZero (SA (ELit 0) (SB + GLZ_LO1 / 8)) (ELit ((GLZ_HI1 - GLZ_LO1) / 8)); KShOk (SA (ELit 0) GLZ_LO1) (ELit (GLZ_HI1 - GLZ_LO1));
   KZero (SA (ELit 0) (SB + GLZ_LO2 / 8)) (ELit ((GLZ_HI2 - GLZ_LO2) / 8)); KShOk (SA (ELit 0) GLZ_LO2) (ELit (GLZ_HI2 - GLZ_LO2));
   KShOk (SA (ELit 0) 0x22b40) (ELit 12);
   KZero (SA (ELit 0) (SB + GLZ_LO0 / 8)) (ELit ((GLZ_HI0 - GLZ_LO0) / 8)); KShOk (SA (ELit 0) GLZ_LO0) (ELit (GLZ_HI0 - GLZ_LO0))].
(* [comment removed for export] *)
Definition FBMAX : Z := 2 ^ 20.
Definition fb_fact (fb : expr) : kentry := KRange fb 1 FBMAX.
Definition GLZ_SH0 : kentry := KZero (SA (ELit 0) (SB + GLZ_LO0 / 8)) (ELit ((GLZ_HI0 - GLZ_LO0) / 8)).
(* [comment removed for export] *)
Definition NEWH : list kentry :=
  [KWord (SA (ELit 0) (g_newh_got GASAN)) 8 (ELit (g_newh_cell GASAN)); KWord (SA (ELit 0) (g_newh_cell GASAN)) 8 (ELit (g_newh_val GASAN))].

(* [comment removed for export] *)
Definition CT0 (id : nat) : option gcallee := None.
Definition XN (IT : itab) (NXF : nat) : nat -> list expr -> acs -> option acs := XNc ASEGS IT AASAN NXF GASAN 0 0 CT0.
(* [comment removed for export] *)
Definition LIMIT : Z := StoreOk.RunLim.LMIN.
Definition FUEL : nat := 2000.
Definition BFUEL : nat := 1000.

(* [comment removed for export] *)
Definition q100w (x : expr) : expr := EAluw ALU_SRL (escale 5243 x) (ELit 19).
Definition q100 (x : expr) : expr := EAlu ALU_SRL (escale 5243 x) (ELit 19).
Definition q1e4a (x : expr) : expr := EAlu ALU_SRL (escale 429497 x) (ELit 32).
Definition q1e4b (x : expr) : expr := EAlu ALU_SRL (escale 109951163 x) (ELit 40).

Definition q1e8h (x : expr) : expr := EAlu ALU_SRL (EMd M_MULHU x (ELit 0xabcc77118461cefd)) (ELit 26).
Definition rem (x q : expr) (d : Z) : expr := rem_expr x q d.
Definition divfact (x q : expr) (d : Z) (k : plan) : plan := PExt 40 [x; q; ELit d] k.
(* [comment removed for export] *)
Definition zfact (x q : expr) (d : Z) (k : plan) : plan :=
  PFact (KRange (escale 4294967296 (rem x q d)) 0 ((d - 1) * 4294967296)) k.


Lemma asan_G_img_al : 0 <= g_img_lo GASAN /\ g_img_lo GASAN mod 8 = 0 /\ g_img_hi GASAN mod 8 = 0.
Proof. cbn. repeat split; reflexivity || lia. Qed.
Lemma asan_G_img_shlo : g_img_hi GASAN <= SHMAPLO.
Proof. cbn. unfold SHMAPLO. lia. Qed.
Lemma nil_SWIN_img : forall lo hi, In (lo, hi) (@nil (Z * Z)) ->
  g_ro_hi GASAN <= lo /\ hi <= g_img_hi GASAN /\ (forall plo phi, In (plo, phi) (g_priv GASAN) -> hi <= plo \/ phi <= lo).
Proof. intros lo hi []. Qed.

(* [comment removed for export] *)
Section XNSound.
Context {RC : run_ceil}.
Variable IT : itab.
Hypothesis IT_ok : itab_sound ASEGS IT.
Variable NXF : nat.
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 ASEGS RZ.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis HP : hprops [] GASAN SHC AINVH.
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable HIDc HIDFc : list (Z * Z).
Variable M0c : word -> option byte.
Variable B0c C0c : Z.
Hypothesis B0c_nonneg : 0 <= B0c.
Hypothesis C0c_nonneg : 0 <= C0c.
Hypothesis bcap_ok : B0c + 0 <= GBUDGET.
Hypothesis ccap_ok : C0c + 0 <= GCOUNT.
Variable FTOPc : Z.
Hypothesis FTOPc_ok : Z.of_nat (length HIDFc) + FTOPc <= FMIN.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree NXF E E' -> UINV E -> UINV E'.
#[local] Notation AINVc := (AINV_f [] GASAN AINVH PERMc SPTOPc HIDc HIDFc M0c B0c C0c).

Theorem XN_sound :
  gcontracts ASEGS IT AASAN NXF PERMc SPTOPc FS0 SHC (VSHf HIDc HIDFc) AINVc KCAP FTOPc fx_ok UINV RZ GASAN 0 0 ->
  GPS.ext_stmt ASEGS NXF (XN IT NXF) PERMc SPTOPc FS0 SHC (VSHf HIDc HIDFc) AINVc KCAP FTOPc fx_ok UINV RZ.
Proof.
  intros GCs. unfold XN.
  exact (XNc_sound ASEGS IT AASAN asan_in_hull asan_hull_ok IT_ok NXF [] GASAN 0 0 fx_ok SHC KCAP AINVH HP
            asan_G_ro_img2 asan_G_img_al asan_G_img_shlo nil_SWIN_img asan_segs_out asan_A_img_hi asan_A_img_lo asan_segs_wx
            PERMc SPTOPc FS0 HIDc HIDFc M0c B0c C0c B0c_nonneg C0c_nonneg bcap_ok ccap_ok FTOPc FTOPc_ok UINV UINV_agree
            RZ RZ_silent1 CT0 ltac:(intros id' ce' H; discriminate H) GCs).
Qed.
End XNSound.

(* [comment removed for export] *)
Definition IXMAX : Z := 32 * 2 ^ 26.
Definition RELHI : Z := 24 * 2 ^ 26 + 256 * IXMAX.
Definition relx (di err ix ix0 : expr) (lo : Z) : kentry :=
  KRange (esub (eadd (escale 24 di) (escale IXMAX err)) (esub ix ix0)) lo RELHI.
