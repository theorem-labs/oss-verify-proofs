From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01 YL0g YI14 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract KindBGlue Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes EntC1_Defs EntC1_Glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterApp WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import WriterRet pj_parse_c check_no_overread_c check_reject_clean_starved_c round_trip_text_c check_round_trip_c LLVMFuzzerTestOneInput_c EntryDefs EntrySR EntBase EntGlue EntSegA EntStg EntSQ_Cnt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require strtod_c.
Import ListNotations.
Local Open Scope Z_scope.

(* The check_round_trip stage of LLVMFuzzerTestOneInput on the #102 ubsan pin (fuzz_preset.c:832-833: `if
   (!check_round_trip(&doc)) check_reject_clean_starved(data, size, count, &doc);`). check_round_trip (0x1408c) is called
   at 0x13848 with doc = sp = S - 112 and returns to 0x1384c. The entry hands it both flag bytes 0 (ent_flags), so its
   contract (check_round_trip_c @ rw102-crt e0ca34385157) gives the normal arm: a0 = 0, the flags stay 0; the ran-out arm
   (a0 = 1) needs a flag set and is false here. The branch `bnez a0` at 0x1384c is then not taken and the code sets up
   check_reject_clean_starved(data, size, took, &doc) (EntSegA.ent_segE2), the next stage stg_crs1_st. *)

(* The registers the entry keeps (ent_rk) survive a call that preserves the callee-saved registers. *)
Lemma ecrt_rk : forall regs0 r1 r2, regs_preserved r1 r2 -> ent_rk regs0 r1 -> ent_rk regs0 r2.
Proof.
  intros regs0 r1 r2 RR (G2 & G3 & G4 & G22 & G23 & G24 & G25 & G26 & G27).
  split; [etransitivity; [apply (RR 2); unfold callee_saved; lia | exact G2]|].
  split; [etransitivity; [apply (RR 3); unfold callee_saved; lia | exact G3]|].
  split; [etransitivity; [apply (RR 4); unfold callee_saved; lia | exact G4]|].
  split; [etransitivity; [apply (RR 22); unfold callee_saved; lia | exact G22]|].
  split; [etransitivity; [apply (RR 23); unfold callee_saved; lia | exact G23]|].
  split; [etransitivity; [apply (RR 24); unfold callee_saved; lia | exact G24]|].
  split; [etransitivity; [apply (RR 25); unfold callee_saved; lia | exact G25]|].
  split; [etransitivity; [apply (RR 26); unfold callee_saved; lia | exact G26]|].
  etransitivity; [apply (RR 27); unfold callee_saved; lia | exact G27].
Qed.

Section S.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.
Hypothesis CRT : forall fx' : YK11.FPState, @check_round_trip_contract fx' rc B API F.
Hypothesis HWL1 : esq_wl1.
Hypothesis HWL2 : esq_wl2.
Hypothesis HESZ : esq_esz.
Hypothesis NEXT : stg_crs1_st (fx := fx) B API F.

(* round_trip_text's relation of a call gives the entry's rstep of it (no block is freed). *)
Lemma ecrt_rstep_rtt : forall K regs E L A mem md L' A' regs' mem' md',
  rtt_rel B API K regs E L A mem md L' A' regs' mem' md' ->
  rstep B API K (spZ regs) E (fun _ => False) L A mem md L' A' mem' md'.
Proof.
  intros K regs E L A mem md L' A' regs' mem' md' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  split; [intros a k Hin _ _; exact (H5 a k Hin)|].
  split; [exact H7|]. split; [exact H8|]. split; [exact H9|].
  split; [intros a k i Hin _ Hi He; exact (H10 a k i Hin Hi He)|].
  exact H11.
Qed.

#[local] Set Default Proof Using "All".

Let AX : AllocExtra B (aa_MR API) := ent_AX B API FA.
Let FG : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a := ent_FG B API FA.

Theorem stg_crt_holds : stg_crt_st (fx := fx) B API F.
Proof.
  unfold stg_crt_st.
  intros stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A regs mem md Lam peak E1 E2 E3 t D
    ENT INV R1 RK R8 R9 R10 R19 FLG HEMP HEMP2 ROOMS HN CNOW JR TREE.
  pose proof RK as (G2 & G3 & G4 & G22 & G23 & G24 & G25 & G26 & G27).
  pose proof FLG as (FL1 & FL2).
  pose proof ENT as ((PRE & HNL & _) & SYMS & _ & _ & SLK & _ & _ & _ & LED0 & CNT0 & HJ & _).
  pose proof PRE as (MR0 & _ & _ & _ & _ & SP16 & SPC & SP63 & _).
  pose proof INV as (RS & Z0 & INIT & RD & FRM & LED & RES & _).
  pose proof TREE as (PL & NODE & TDL & NEW).
  pose proof alloc_ceiling_val as HCV. pose proof alloc_ceiling_lt as HCL.
  assert (HK : SLOT_K = 14704) by reflexivity.
  assert (HCK : CRT_K = 14592) by reflexivity.
  assert (SPr : spZ regs = spZ regs0 - 112) by (unfold spZ at 1; rewrite G2; apply EMS.unsigned_lit; lia).
  assert (RET : YK0s.ret_ok (getr regs 1)) by (rewrite R1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity).
  pose proof (ent_env_mid B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A mem md
    Lam peak (ent_c3 cnt0 pl) (ent_b3 F b0 pl E1 E2 E3 []) regs CRT_K ENT INV SPr G4 RET
    ltac:(lia) ltac:(lia)) as REN.
  assert (HC0 : 0 <= cnt0 <= Z.of_nat j * 2 ^ 60) by (pose proof LED0 as (_ & _ & H & _); lia).
  pose proof (esq_c3 cnt0 pl j HC0 HJ HN) as HC3.
  pose proof (esq_zb_len pl) as ZL.
  pose proof CNOW as (C1 & C2 & C3).
  destruct (ROOMS HN) as (_ & RM).
  destruct (RM E1 E2 E3 C1 C2 C3) as (_ & RMJ). rewrite JR in RMJ. destruct RMJ as (_ & (RT1 & RT2 & RT3) & _).
  assert (DL : forall bk, In bk D -> In bk Lam)
    by (intros bk H; exact (Permutation_in _ (Permutation_sym PL) H)).
  eapply SR_bind.
  { exact (CRT fx1 L A regs mem md Lam peak (ent_c3 cnt0 pl) (ent_b3 F b0 pl E1 E2 E3 []) (spZ regs0 - 112) t D
      (zb pl) 0 0 REN INIT LED (proj2 HC3) RES R10 NODE DL ltac:(lia) JR ltac:(lia)
      (HWL1 (zb pl) t JR ltac:(lia)) (HWL2 (zb pl) t JR ltac:(lia)) RT1 RT2 RT3 (HESZ (zb pl) t JR ltac:(lia))
      ltac:(lia) ltac:(lia) FL1 FL2). }
  intros c' (fx2 & L' & A' & regs2 & mem2 & md2 & Lam' & peak' & cset & b' & -> & FRM2 & _ & RR & RD2 & INIT2 &
    FB1 & FB2 & ARMS).
  destruct ARMS as [(HRO & _) | (_ & _ & A10 & HCS & _ & LED2 & PK2 & PERM2 & RES2 & CFIN & NODE2)];
    [exfalso; lia|].
  rewrite R1.
  pose proof RR as (M2 & _ & _ & _ & BK & RR2 & _).
  pose proof (ecrt_rstep_rtt CRT_K regs alloc_statics L A mem md L' A' regs2 mem2 md2 RR) as STEP.
  rewrite SPr in STEP.
  assert (INV2 : ent_inv B API F stk L0 A0 regs0 mem0 md0 p n fx2 L' A' mem2 md2 Lam' peak'
      (ent_c4 cnt0 pl t cset) b').
  { apply (ent_after B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A mem md Lam peak
      (ent_c3 cnt0 pl) (ent_b3 F b0 pl E1 E2 E3 []) CRT_K alloc_statics (fun _ => False)
      fx2 L' A' mem2 md2 Lam' peak' (ent_c4 cnt0 pl t cset) b' ENT INV STEP); try (unfold CRT_K; lia).
    - intros a Ha. left. left. exact Ha.
    - intros a Ha Hs. pose proof (ent_statics_lo _ Hs). lia.
    - intros a k Hin _. exact (BK a k Hin).
    - exact (proj1 RD2).
    - exact FRM2.
    - exact LED2.
    - exact RES2. }
  pose proof (ecrt_rk regs0 regs regs2 RR2 RK) as (G2' & G3' & G4' & G22' & G23' & G24' & G25' & G26' & G27').
  assert (R8' : getr regs2 8 = Z_to_bv 64 n)
    by (etransitivity; [apply (RR2 8); unfold callee_saved; lia | exact R8]).
  assert (R9' : getr regs2 9 = Z_to_bv 64 p)
    by (etransitivity; [apply (RR2 9); unfold callee_saved; lia | exact R9]).
  assert (R19' : getr regs2 19 = Z_to_bv 64 (ent_took pl))
    by (etransitivity; [apply (RR2 19); unfold callee_saved; lia | exact R19]).
  destruct (kb_md B API L' A' mem2 md2 M2) as (Hh2 & Hz2).
  eapply (ent_kA B HSEG fx2 regs2 _ mem2 md2 _ _ Hh2 Hz2).
  { unfold rmk. rewrite G2', A10.
    exact (ent_segE2 (getr regs2 1) (getr regs2 3) (getr regs2 4) (getr regs2 5) (getr regs2 6) (getr regs2 7)
      (getr regs2 8) (getr regs2 9) (getr regs2 11) (getr regs2 12) (getr regs2 13) (getr regs2 14)
      (getr regs2 15) (getr regs2 16) (getr regs2 17) (getr regs2 18) (getr regs2 19) (getr regs2 20)
      (getr regs2 21) (getr regs2 22) (getr regs2 23) (getr regs2 24) (getr regs2 25) (getr regs2 26)
      (getr regs2 27) (getr regs2 28) (getr regs2 29) (getr regs2 30) (getr regs2 31)
      (@fp_regs fx2) (@fp_csr fx2) mem2 (spZ regs0 - 112)). }
  { intros ms' E. eexists _, _, _. exact E. }
  intros R pc' mem3 regs3 HQ HGr.
  ent_inj HQ R pc' mem3.
  apply (NEXT stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx2 L' A' regs3 mem2 md2 Lam' peak' E1 E2 E3
    t D cset b' ENT INV2).
  - rewrite HGr. reflexivity.
  - split; [rewrite HGr; reflexivity|].
    split; [rewrite HGr; transitivity (getr regs2 3); [reflexivity | exact G3']|].
    split; [rewrite HGr; transitivity (getr regs2 4); [reflexivity | exact G4']|].
    split; [rewrite HGr; transitivity (getr regs2 22); [reflexivity | exact G22']|].
    split; [rewrite HGr; transitivity (getr regs2 23); [reflexivity | exact G23']|].
    split; [rewrite HGr; transitivity (getr regs2 24); [reflexivity | exact G24']|].
    split; [rewrite HGr; transitivity (getr regs2 25); [reflexivity | exact G25']|].
    split; [rewrite HGr; transitivity (getr regs2 26); [reflexivity | exact G26']|].
    rewrite HGr; transitivity (getr regs2 27); [reflexivity | exact G27'].
  - rewrite HGr. transitivity (getr regs2 8); [reflexivity | exact R8'].
  - rewrite HGr. transitivity (getr regs2 9); [reflexivity | exact R9'].
  - rewrite HGr. transitivity (getr regs2 9); [reflexivity | exact R9'].
  - rewrite HGr. transitivity (getr regs2 8); [reflexivity | exact R8'].
  - rewrite HGr. transitivity (getr regs2 19); [reflexivity | exact R19'].
  - rewrite HGr. reflexivity.
  - exact (conj FB1 FB2).
  - exact HEMP.
  - exact HEMP2.
  - exact ROOMS.
  - exact HN.
  - exact CNOW.
  - exact JR.
  - split; [exact (Permutation_trans PERM2 PL)|]. split; [exact NODE2|]. split; [exact TDL | exact NEW].
  - exact HCS.
  - exact CFIN.
Qed.

End S.
