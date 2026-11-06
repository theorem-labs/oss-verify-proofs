(* parse_noting (ubsan build, cut-free form): the walk of parse_noting on the #102 binary, and parse_noting_holds,
   which proves the CF parse_noting_c.parse_noting_contract (SR is SRCF's SRcf). The proof text is
   lib/U/Prog/parse_noting.v's; as in lib/U/Prog/CF/pj_parse.v, only the imports change: the CF ReaderKB, pj_parse_c,
   parse_noting_c and SRCF.

   Code (capstone listing of pau-preset-102/omx-clap-core/unstripped/fuzz_preset/fuzz_preset.ubsan, sha256
   27566683952ebd54..., the unstripped twin of the pin 45b0357d18ff66cd...; symbol parse_noting FUNC LOCAL 0x13a38
   size 120; call targets resolved through the ELF's symbol table):
     13a38 addi sp,sp,-0x30     13a3c sd ra,0x28(sp)   13a40 sd s0,0x20(sp)   13a44 sd s1,0x18(sp)
     13a48 sd s2,0x10(sp)       13a4c sd s3,8(sp)
     13a50 mv s0,a2             13a54 mv s2,a1         13a58 mv s3,a0
     13a5c jal fuzz_alloc_live (0x15f34)               13a60 mv s1,a0
     13a64 mv a0,s3             13a68 mv a1,s2         13a6c mv a2,s0
     13a70 jal pj_parse (0x15fb4)                      13a74 mv s2,a0
     13a78 jal fuzz_alloc_ran_out (0x15f90)            13a7c beqz a0,0x13a90
     13a80 mv a0,s2  13a84 mv a1,s0  13a88 mv a2,s1  13a8c jal check_reject_clean (0x13bec)   (not reached: a0 = 0)
     13a90 mv a0,s2             13a94 ld ra,0x28(sp)   13a98 ld s0,0x20(sp)   13a9c ld s1,0x18(sp)
     13aa0 ld s2,0x10(sp)       13aa4 ld s3,8(sp)      13aa8 addi sp,sp,0x30  13aac ret
   The same instructions and registers as the plain build's at other addresses: UBSan instruments nothing here any more
   (the old store to *ran_out and its alignment trap are gone).  The frame's low 8 bytes (sp .. sp + 8) are never
   written.  Source: fuzz_preset.c of #102, lines 499-507 (no int *ran_out, no fuzz_alloc_ran_out_reset).
   The 0 that fuzz_alloc_ran_out returns: the caller hands in g_ran_out = 0 (the contract's premise), the prologue writes
   only the frame, and pj_parse keeps g_ran_out because pj_parse_contract's rpost keeps every image byte that no
   allocator state owns and that is not in pj_parse_writes; globals_free B API omx_G says that no allocator state owns
   g_ran_out.  The proof names no image address: g_ran_out's facts come from globals_free, the alloc statics' and
   errno's bounds from their definitions. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import ReaderKB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require
  fuzz_alloc_live_c fuzz_alloc_ran_out_reset_c fuzz_alloc_ran_out_c.
Import ListNotations.
Open Scope Z_scope.

(* From the entry 0x13a38 to the entry of pj_parse (0x15fb4), across fuzz_alloc_live. *)
Definition pn_pro_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    live : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists m' : word -> option byte,
    ms' = MS (mkR (Z_to_bv 64 0x13a74) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 a2 live
                  a0 a1 a2 a3 a4 a5 a6 a7 a1 a0 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x15fb4) fc None m' (seg_rom rsegs) /\
    (exists j, rw_cells rsegs m' (bv_unsigned sp + -48) [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) /\
    munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m' /\
    wmono rsegs m m'.

Lemma pn_pro : fuzz_alloc_live_c.fuzz_alloc_live_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (live : word),
  stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> 2 ^ 33 <= lo ->
  bytes_at rsegs m fuzz_alloc_live_c.G_LIVE (le8 live) ->
  evt rsegs (pn_pro_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               live F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13a38) fc None m (seg_rom rsegs)).
Proof.
  intros LIVEC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo live ST LO HI BL.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  assert (EL : fuzz_alloc_live_c.G_LIVE + 8 <= 2 ^ 33) by (unfold fuzz_alloc_live_c.G_LIVE; lia).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  do 10 zstep.
  eapply evt_cut; [eapply LIVEC; exact BL |].
  intros ms' ->.
  match goal with |- context [ret_pc (Z_to_bv 64 ?k)] =>
    replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) by (apply bv_eq; vm_compute; reflexivity) end.
  do 5 zstep.
  apply evt_done. unfold pn_pro_post. eexists.
  split; [reflexivity|]. split; [eexists; exact FR|]. split; [exact MU | exact WM].
Qed.

(* From the return of pj_parse (0x13a74) to the return of parse_noting, across fuzz_alloc_ran_out; the branch to
   check_reject_clean (0x13a7c) is not taken because fuzz_alloc_ran_out returns the 0 in g_ran_out.  No step writes
   memory. *)
Definition pn_ret (rav sp gp tp s0v s1v s2v s3v s4 s5 s6 s7 s8 s9 s10 s11 a0 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0' t1' t2' s0v s1v a0 a1' a2' a3' a4' a5' a6' a7'
                  s2v s3v s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc rav) fc None m (seg_rom rsegs).

Lemma pn_tail : fuzz_alloc_ran_out_c.fuzz_alloc_ran_out_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (rav s0v s1v s2v s3v : word) (j : list byte),
  rw_cells rsegs m (bv_unsigned sp) [CB 8 j; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] -> bv_unsigned sp + 48 < 2 ^ 64 ->
  bytes_at rsegs m fuzz_alloc_ran_out_c.G_RAN_OUT (le1 (Z_to_bv 64 0)) ->
  evt rsegs (pn_ret rav sp gp tp s0v s1v s2v s3v s4 s5 s6 s7 s8 s9 s10 s11 a0 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13a74) fc None m (seg_rom rsegs)).
Proof.
  intros RANC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m rav s0v s1v s2v s3v j FR HS BZ.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 2 zstep.
  eapply evt_cut; [eapply RANC with (ran_out := Z_to_bv 64 0); [vm_compute; reflexivity | exact BZ] |].
  intros ms' ->. clear BZ.
  match goal with |- context [ret_pc (Z_to_bv 64 ?k)] =>
    replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) by (apply bv_eq; vm_compute; reflexivity) end.
  zstep. try if_true.
  do 8 zstep.
  apply evt_done. unfold pn_ret. do 14 eexists. reflexivity.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m
YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL0b.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require YK14.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import Regs6ss RegisterBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger GIInit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import pj_parse_c parse_noting_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require strtod_c check_reject_clean_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Module YK11 := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable.YK11.
Module YM05 := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable.YM05.
Module Mem := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Mem.
Module Frame := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Frame.
Module MemNorm := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.MemNorm.
Module strtod_c := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.
Local Open Scope Z_scope.

(* A disjunction parked out of lia's sight until a step needs it. *)
Local Definition hide (P : Prop) : Prop := P.

Lemma pn_bytes_mbyte : forall m m' a bs, Mem.bytes_at rsegs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
  Mem.bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (H1 & H2 & H) K. split; [exact H1|]. split; [exact H2|]. intros i Hi.
  change (mbyte rsegs m' (a + Z.of_nat i) = nth_error bs i). rewrite (K (Z.of_nat i)) by lia. exact (H i Hi).
Qed.

Lemma pn_ro_munch : forall m m' W, MemNorm.ro_agree rsegs m -> munch W m m' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> Mem.ro_addr rsegs (Z_to_bv 64 x) = false) ->
  MemNorm.ro_agree rsegs m'.
Proof.
  intros m m' W H MU HW a Ha.
  destruct (rk_outside_dec W (bv_unsigned a)) as [Ho|Ho].
  - unfold Mem.mrd. rewrite (MU a Ho). exact (H a Ha).
  - exfalso. pose proof (bv_unsigned_in_range 64 a) as R. change (bv_modulus 64) with (2 ^ 64) in R.
    pose proof (HW (bv_unsigned a) R Ho) as E. rewrite Z_to_bv_lit_self in E. rewrite E in Ha. discriminate Ha.
Qed.

(* The return registers: s0 .. s3 and ra come back from the frame, s4 .. s11, gp and tp were never written. *)
Lemma pn_final_regs : forall regs regs2 R' x5 x6 x7 v x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
  xregs_eqv (mkR (reg_get regs 1) (Z_to_bv 64 (bv_unsigned (reg_get regs2 2) + 48)) (reg_get regs2 3) (reg_get regs2 4)
     x5 x6 x7 (reg_get regs 8) (reg_get regs 9) v x11 x12 x13 x14 x15 x16 x17
     (reg_get regs 18) (reg_get regs 19) (reg_get regs2 20) (reg_get regs2 21) (reg_get regs2 22) (reg_get regs2 23)
     (reg_get regs2 24) (reg_get regs2 25) (reg_get regs2 26) (reg_get regs2 27) x28 x29 x30 x31) R' ->
  spZ regs2 + 48 = spZ regs ->
  (forall r, r = 3 \/ r = 4 \/ 20 <= r <= 27 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  regs_preserved regs R' /\ getr R' 10 = v.
Proof.
  intros regs regs2 R' x5 x6 x7 v x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 XR HS CS.
  split; [|rewrite (rk_getr_eqv _ _ XR); reflexivity].
  intros r Hr. unfold callee_saved in Hr. rewrite (rk_getr_eqv _ _ XR).
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
               r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
  - change (Z_to_bv 64 (bv_unsigned (reg_get regs2 2) + 48) = getr regs 2).
    change (bv_unsigned (reg_get regs2 2)) with (spZ regs2). rewrite HS. exact (Z_to_bv_lit_self (getr regs 2)).
  - exact (CS 3 ltac:(lia)).
  - exact (CS 4 ltac:(lia)).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact (CS 20 ltac:(lia)).
  - exact (CS 21 ltac:(lia)).
  - exact (CS 22 ltac:(lia)).
  - exact (CS 23 ltac:(lia)).
  - exact (CS 24 ltac:(lia)).
  - exact (CS 25 ltac:(lia)).
  - exact (CS 26 ltac:(lia)).
  - exact (CS 27 ltac:(lia)).
Qed.

(* Membership in a globals list by computation, so that no proof below depends on the position of an entry. *)
Lemma pn_glob_dec : forall G a,
  existsb (fun e => (fst e <=? a) && (a <? fst e + snd e)) G = true -> in_globals G a.
Proof.
  intros G a H. apply existsb_exists in H. destruct H as ([lo len] & Hin & Hb).
  apply andb_prop in Hb. destruct Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  cbn [fst snd] in H1, H2. exists lo, len. split; [exact Hin | lia].
Qed.

Section KB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable RF : ResForm.
Hypothesis SEG : ms_segs B = rsegs.
Hypothesis HG : globals_free B API omx_G.
(* g_ran_out is an entry of omx_G (lib/U/Prog/GIInit.v). *)
Lemma pn_grg : in_globals omx_G fuzz_alloc_ran_out_c.G_RAN_OUT.
Proof. apply pn_glob_dec. vm_compute. reflexivity. Qed.

Lemma pn_lsum_nonneg : forall L A m l pk c f, ledger B L A m l pk c f -> 0 <= lsum l.
Proof.
  intros L A m l pk c f (_ & _ & _ & _ & _ & FB). clear -FB. induction FB as [|[a k] l Hk _ IH]; cbn [lsum]; [lia|].
  destruct Hk as (Hk & _). cbn [snd] in Hk. lia.
Qed.

Lemma pn_main : fuzz_alloc_live_c.fuzz_alloc_live_contract ->
  pj_parse_contract B API RF -> fuzz_alloc_ran_out_c.fuzz_alloc_ran_out_contract ->
  parse_noting_contract B API RF.
Proof.
  intros LIVEC PJ RANC. unfold parse_noting_contract.
  intros L A regs mem md Lam peak cnt fail b t0 len out tb ENV LG RES R10 R11 R12 LEN T0 TE TL TB MXR TOK ONZ
    PRW RPL OUTL DJT BZ0 DJG DJS CNT ROOM.
  pose proof ENV as (_ & TP & ERR & GG & GD & PRE & SP47 & GTOP & FRM & RDC).
  pose proof PRE as (HM & HWF & HBD & HRA & H16 & HAC & H63 & HWS & HTP & HER & HAUX).
  destruct (mr_model B _ (aa_laws API) L A mem md HM) as (Hh & Hl & Hmt).
  pose proof RDC as (RO & RGG & RGD).
  pose proof RPL as (PLC & PAUX & PEX).
  pose proof rk_ceil as HCEIL.
  pose proof (zr_word (getr regs 2)) as Rsp. unfold inr64 in Rsp. change (bv_unsigned (getr regs 2)) with (spZ regs) in Rsp.
  assert (KP : 0 <= PJ_PARSE_K) by (vm_compute; discriminate).
  assert (HK : 48 + PJ_PARSE_K <= PN_K /\ 64 <= PN_K).
  { unfold PN_K, PN_F. pose proof (Z.le_max_l PJ_PARSE_K check_reject_clean_c.CHECK_REJECT_CLEAN_FRAME) as M1.
    pose proof (Z.le_max_r PJ_PARSE_K check_reject_clean_c.CHECK_REJECT_CLEAN_FRAME) as M2.
    unfold check_reject_clean_c.CHECK_REJECT_CLEAN_FRAME in *. lia. }
  cbn [Frame.disjoint_from] in DJT, DJG, DJS.
  destruct DJS as (DS1 & DS2 & _). destruct DJG as (_ & DG2 & _). destruct DJT as (DT1 & _).
  assert (HDS1 : hide (spZ regs - PN_K + PN_K <= t0 \/ t0 + len <= spZ regs - PN_K)) by exact DS1.
  assert (HDS2 : hide (spZ regs - PN_K + PN_K <= out \/ out + 56 <= spZ regs - PN_K)) by exact DS2.
  assert (HDG2 : hide (fuzz_alloc_ran_out_c.G_RAN_OUT + 1 <= out \/ out + 56 <= fuzz_alloc_ran_out_c.G_RAN_OUT))
    by exact DG2.
  assert (HDT1 : hide (out + 56 <= t0 \/ t0 + len <= out)) by exact DT1.
  clear DS1 DS2 DG2 DT1.
  rewrite SEG in RO, HWS, PRW, TB, BZ0.
  destruct (HG fuzz_alloc_ran_out_c.G_RAN_OUT pn_grg) as (GIMG & GLO & _ & GERR & GNO).
  pose proof (rk_img_bound SEG _ GIMG) as GRB.
  assert (GNOW : forall L0 A0 mem0 md0, aa_MR API L0 A0 mem0 md0 -> ~ owned B L0 A0 fuzz_alloc_ran_out_c.G_RAN_OUT)
    by (intros L0 A0 mem0 md0 H0; exact (proj1 (GNO L0 A0 mem0 md0 H0))).
  assert (OWL : forall L0 A0 mem0 md0 x, aa_MR API L0 A0 mem0 md0 -> owned B L0 A0 x -> 0 <= x < alloc_ceiling)
    by (intros L0 A0 mem0 md0 x HM0 Ho; exact (mr_owned_low B _ (aa_laws API) L0 A0 mem0 md0 x HM0 Ho)).
  assert (STL : forall a, alloc_statics a -> 0 <= a < 2 ^ 33)
    by (intros a Ha; unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha; lia).
  assert (STG : forall a, alloc_statics a -> a <> fuzz_alloc_ran_out_c.G_RAN_OUT)
    by (intros a Ha; unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha;
        unfold fuzz_alloc_ran_out_c.G_RAN_OUT; lia).
  assert (ERRL : errno_addr B < 2 ^ 33) by (rewrite ERR; unfold strtod_c.STRTOD_ERRNO; lia).
  assert (ES : bv_unsigned (reg_get regs 2) = spZ regs) by reflexivity.
  assert (BL : Mem.bytes_at rsegs mem fuzz_alloc_live_c.G_LIVE (Mem.le8 (Z_to_bv 64 (lsum Lam)))).
  { pose proof LG as ((W1 & _) & HLP & _). pose proof (pn_lsum_nonneg _ _ _ _ _ _ _ LG) as Hl0.
    unfold fuzz_alloc_live_c.G_LIVE. unfold G_LIVE in W1. rewrite <- SEG.
    apply (word_mem_le8 (ms_segs B)); [exact W1 | lia | lia | lia]. }
  match goal with |- SR _ _ ?P => set (POST := P) end.
  rewrite SEG. unfold PARSE_NOTING.
  (* the prologue and the call to fuzz_alloc_live *)
  eapply rk_kA; [exact Hh | exact Hl | |].
  { unfold mkR_of.
    apply (pn_pro LIVEC) with (lo := spZ regs - PN_K) (live := Z_to_bv 64 (lsum Lam)).
    - rewrite ES. apply rk_stk_of_wr; [lia | lia | exact HWS].
    - rewrite ES. lia.
    - lia.
    - exact BL. }
  intros ms1 (can & PQ & EQV). destruct PQ as (m1 & -> & (j & FR1) & MU1 & WM1).
  destruct (rk_eqv_shape _ _ _ _ _ _ EQV) as (Ems & XR). rewrite Ems. clear Ems EQV.
  revert XR. generalize (ms_regs ms1) as regs1. intros regs1 XR. clear ms1.
  rewrite ES in FR1, MU1.
  assert (G1 : getr regs1 1 = Z_to_bv 64 0x13a74) by (rewrite (rk_getr_eqv _ _ XR); reflexivity).
  assert (S1 : spZ regs1 = spZ regs - 48).
  { unfold spZ. rewrite (rk_getr_eqv _ _ XR).
    change (bv_unsigned (Z_to_bv 64 (bv_unsigned (reg_get regs 2) + -48)) = spZ regs - 48).
    rewrite ES. rewrite unsigned_lit by lia. lia. }
  assert (G10 : getr regs1 10 = Z_to_bv 64 t0) by (rewrite (rk_getr_eqv _ _ XR); exact R10).
  assert (G11 : getr regs1 11 = Z_to_bv 64 len) by (rewrite (rk_getr_eqv _ _ XR); exact R11).
  assert (G12 : getr regs1 12 = Z_to_bv 64 out) by (rewrite (rk_getr_eqv _ _ XR); exact R12).
  assert (GK : forall r, r = 3 \/ r = 4 \/ 20 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr. rewrite (rk_getr_eqv _ _ XR).
    assert (Hc : r = 3 \/ r = 4 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; reflexivity. }
  clear XR.
  assert (OUTW : forall x, 0 <= x < alloc_ceiling -> outside [(spZ regs + -48, spZ regs)] x).
  { intros x Hx. cbn [outside]. split; [lia | exact I]. }
  assert (OWK1 : forall x, owned B L A x -> mbyte (ms_segs B) m1 x = mbyte (ms_segs B) mem x).
  { intros x Ho. pose proof (OWL _ _ _ _ x HM Ho).
    apply (MemNorm.mbyte_munch _ _ _ _ _ MU1); [lia | apply OUTW; lia]. }
  assert (HM1 : aa_MR API L A m1 md).
  { eapply (mr_frame B _ (aa_laws API) L A mem m1 md md HM).
    - exact OWK1.
    - intros a Ho (b0 & Hb0). pose proof (OWL _ _ _ _ a HM Ho) as Ha. exists b0.
      rewrite (MU1 (Z_to_bv 64 a)); [exact Hb0|]. rewrite unsigned_lit by lia. apply OUTW; lia.
    - intros p n i Hp Hi. destruct (mr_blocks B _ (aa_laws API) L A mem md p n i HM Hp Hi) as ((b0 & Hb0) & R1 & R2 & _).
      exists b0. rewrite (MU1 (Z_to_bv 64 (ptr_addr L p + i))); [exact Hb0|]. rewrite unsigned_lit by lia.
      apply OUTW; lia.
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmt. }
  assert (WM1' : wmono (ms_segs B) mem m1) by (rewrite SEG; exact WM1).
  assert (LG1 : ledger B L A m1 Lam peak cnt fail).
  { apply (rk_ledger_keep L A mem m1 Lam peak cnt fail LG).
    - intros a Ha. pose proof (STL a Ha).
      apply (MemNorm.mbyte_munch _ _ _ _ _ MU1); [lia | apply OUTW; lia].
    - intros a k i HI Hi. pose proof (ledger_block_range B API L A mem md Lam peak cnt fail a k HM LG HI) as (Ra & Rb & _).
      pose proof LG as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF. destruct (HF _ HI) as (Hk & _).
      cbn [fst snd] in Hk.
      apply (MemNorm.mbyte_munch _ _ _ _ _ MU1); [lia | apply OUTW; lia]. }
  assert (TB1 : Mem.bytes_at rsegs m1 t0 tb).
  { apply (bytes_at_transport rsegs _ mem m1 t0 tb TB MU1). rewrite TL. cbn [disjoint_from].
    unfold hide in HDS1. lia. }
  assert (PRW1 : pj_rw rsegs m1 out).
  { destruct PRW as [AL PS]. split; [exact AL|].
    apply (stk_transport_disjoint rsegs _ mem m1 out (out + 56) PS MU1 WM1). cbn [disjoint_from].
    unfold hide in HDS2. lia. }
  assert (BZ1 : Mem.bytes_at rsegs m1 fuzz_alloc_ran_out_c.G_RAN_OUT (Mem.le1 (Z_to_bv 64 0))).
  { apply (bytes_at_transport rsegs _ mem m1 _ _ BZ0 MU1). cbn [disjoint_from]. rewrite Mem.length_le1.
    change (Z.of_nat 1) with 1. split; [lia | exact I]. }
  assert (ROW : forall x, 0 <= x < 2 ^ 64 -> ~ outside [(spZ regs + -48, spZ regs)] x ->
    Mem.ro_addr rsegs (Z_to_bv 64 x) = false).
  { intros x Hx Ho. cbn [outside] in Ho. unfold Mem.ro_addr. rewrite unsigned_lit by lia.
    rewrite rk_high_nofs by lia. reflexivity. }
  assert (RDC1 : rd_cells B m1).
  { split; [rewrite SEG; exact (pn_ro_munch mem m1 _ RO MU1 ROW)|]. split.
    - apply (rk_word_keep mem m1 _ _ RGG). intros k Hk. apply OWK1. right. unfold static_owned. do 4 right. left. lia.
    - destruct RGD as (g & Hg). exists g. apply (rk_word_keep mem m1 _ _ Hg). intros k Hk. apply OWK1. right.
      unfold static_owned. do 5 right. left. lia. }
  assert (LIBK1 : forall i, 0 <= i < 8 ->
    mbyte (ms_segs B) m1 (ms_libc B + 8 + i) = mbyte (ms_segs B) mem (ms_libc B + 8 + i)).
  { intros i Hi. apply OWK1. right. unfold static_owned. right; right; left; lia. }
  assert (HIK1 : forall a, spZ regs <= a < 2 ^ 63 -> mbyte (ms_segs B) m1 a = mbyte (ms_segs B) mem a).
  { intros a Ha. apply (MemNorm.mbyte_munch _ _ _ _ _ MU1); [lia | cbn [outside]; split; [lia | exact I]]. }
  assert (AUX1 : st_init_done A = false -> auxv_pre B (ly_sec L) (spZ regs1) m1).
  { intros HI. rewrite S1. eapply auxv_pre_mono; [| apply (rk_auxv_keep _ _ mem m1 (HAUX HI) LIBK1 HIK1)]. lia. }
  assert (RPL1 : rplace B L A Lam regs1 m1 out).
  { split; [|split; [|exact PEX]].
    - unfold pj_place in PLC |- *.
      destruct PLC as [P1|[P2|P3]]; [left; rewrite S1; lia | right; left; exact P2 | right; right; exact P3].
    - intros Hs HI. rewrite S1 in Hs.
      assert (Ho : spZ regs <= out) by (unfold hide in HDS2; lia).
      apply (rk_auxv_keep _ _ mem m1 (PAUX Ho HI) LIBK1). intros a Ha. apply HIK1. lia. }
  assert (TOK1 : text_ok B L A Lam regs1 t0 len).
  { destruct TOK as [TK1 TK2]. split; [|exact TK2].
    destruct TK1 as [H|H]; [left; rewrite S1; lia | right; exact H]. }
  assert (LB1 : 0 <= ms_libc B + 8 /\ ms_libc B + 16 <= alloc_ceiling).
  { pose proof (OWL _ _ _ _ (ms_libc B + 8) HM ltac:(right; unfold static_owned; right; right; left; lia)).
    pose proof (OWL _ _ _ _ (ms_libc B + 15) HM ltac:(right; unfold static_owned; right; right; left; lia)). lia. }
  assert (RPA : rpost B API PN_K L A regs mem md (parse_noting_writes out) (fun _ _ => False) L A regs m1 md).
  { eapply (rk_of_A SEG PN_K L A regs mem md _ m1 _ regs HM1 HWF HBD).
    - intros r _. reflexivity.
    - exact MU1.
    - exact WM1'.
    - intros a [Ha|Ha]; [rewrite SEG; apply HWS; exact Ha | apply HER; exact Ha].
    - intros x Hx Hs He. unfold scratch_k in Hs. cbn [outside]. split; [lia | exact I].
    - intros i Hi. apply OUTW. lia.
    - lia.
    - lia.
    - intros p n i Hp Hi He. destruct (mr_blocks B _ (aa_laws API) L A mem md p n i HM Hp Hi) as (_ & R1 & R2 & _).
      split; [lia|]. apply OUTW; lia. }
  (* pj_parse *)
  rewrite <- SEG.
  eapply SR_bind.
  { apply (PJ L A regs1 m1 md Lam peak cnt fail b t0 len out tb).
    - split; [exact SEG|]. split; [exact TP|]. split; [exact ERR|]. split; [exact GG|]. split; [exact GD|].
      split.
      { split; [exact HM1|]. split; [exact HWF|]. split; [exact HBD|].
        split; [rewrite G1; apply ret_ok_even; vm_compute; reflexivity|].
        split; [rewrite S1; Z.div_mod_to_equations; lia|].
        split; [rewrite S1; lia|].
        split; [rewrite S1; lia|].
        split; [intros a Ha; rewrite S1 in Ha; unfold writable_at; apply WM1'; rewrite SEG; apply HWS; lia|].
        split; [transitivity (getr regs1 (Z_to_bv 5 4)); [reflexivity|]; rewrite (GK 4 ltac:(lia)); exact HTP|].
        split; [intros a Ha; unfold writable_at; apply WM1'; apply HER; exact Ha|].
        exact AUX1. }
      split; [rewrite S1; lia|]. split; [rewrite S1; lia|]. split; [exact FRM|]. exact RDC1.
    - exact LG1.
    - exact RES.
    - exact G10.
    - exact G11.
    - exact G12.
    - exact LEN.
    - exact T0.
    - exact TE.
    - exact TL.
    - rewrite SEG. exact TB1.
    - exact MXR.
    - exact TOK1.
    - exact ONZ.
    - rewrite SEG. exact PRW1.
    - exact RPL1.
    - exact OUTL.
    - cbn [disjoint_from]. unfold hide in HDT1. lia.
    - rewrite S1. cbn [disjoint_from]. unfold hide in HDS1, HDS2. lia.
    - exact CNT.
    - exact ROOM. }
  intros c2 (fx2 & L1 & A1 & regs2 & mem2 & md1 & Lam1 & peak1 & cnt1 & fail1 & ok & res & tr & -> & FRM2 & FK2 & RP2 &
    RDC2 & LG2 & JV & OKS & CNT1 & FA1 & PK1 & HP1 & IMP1 & IMP2 & ARM).
  pose proof RP2 as (M2 & WF2 & B2 & Y2 & I2 & X2 & G2' & S2' & P2 & RP2r & D2 & H2 & IM2 & K2 & C2).
  destruct (mr_model B _ (aa_laws API) L1 A1 mem2 md1 M2) as (Hh1 & Hl1 & _).
  assert (SP2 : spZ regs2 = spZ regs - 48).
  { rewrite <- S1. unfold spZ. change (bv_unsigned (getr regs2 (Z_to_bv 5 2)) = bv_unsigned (getr regs1 (Z_to_bv 5 2))).
    rewrite (RP2r 2); [reflexivity | unfold callee_saved; lia]. }
  assert (GK2 : forall r, r = 3 \/ r = 4 \/ 20 <= r <= 27 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr. rewrite (RP2r r); [exact (GK r Hr) | unfold callee_saved; lia]. }
  assert (NS1 : forall a, spZ regs - 48 <= a < 2 ^ 64 -> ~ scratch_k B PJ_PARSE_K regs1 a).
  { intros a Ha. unfold scratch_k. rewrite S1. lia. }
  assert (KEEP2 : forall a, spZ regs - 48 <= a < 2 ^ 64 -> ~ (out <= a < out + 56) ->
    mbyte (ms_segs B) mem2 a = mbyte (ms_segs B) m1 a /\
    (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) mem2 a)).
  { intros a Ha Ho. apply H2; [lia | exact (NS1 a Ha) |].
    unfold pj_parse_writes. intros [Hx|Hst]; [exact (Ho Hx) | pose proof (STL a Hst); lia]. }
  assert (SAV2 : rw_cells rsegs mem2 (spZ regs + -48)
    [CB 8 j; C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
     C8 (reg_get regs 1)]).
  { apply (rk_rw_cells_keep m1 mem2 _ _ FR1). intros i Hi. cbn in Hi.
    destruct (KEEP2 (spZ regs + -48 + i)) as [E1 E2]; [lia | unfold hide in HDS2; lia |].
    rewrite SEG in E1, E2. split; [exact E1 | tauto]. }
  assert (BZ2 : Mem.bytes_at rsegs mem2 fuzz_alloc_ran_out_c.G_RAN_OUT (Mem.le1 (Z_to_bv 64 0))).
  { apply (pn_bytes_mbyte m1 mem2 _ _ BZ1). intros i Hi. rewrite Mem.length_le1 in Hi. change (Z.of_nat 1) with 1 in Hi.
    replace i with 0 by lia. rewrite Z.add_0_r. rewrite <- SEG.
    refine (proj1 (IM2 _ GIMG GNOW _ _)).
    - unfold scratch_k. rewrite S1. lia.
    - unfold pj_parse_writes. intros [Hx|Hst]; [unfold hide in HDG2; lia | exact (STG _ Hst eq_refl)]. }
  (* the call to fuzz_alloc_ran_out, the untaken branch to check_reject_clean, and the epilogue *)
  rewrite G1, SEG.
  eapply rk_kA; [exact Hh1 | exact Hl1 | |].
  { unfold mkR_of.
    apply (pn_tail RANC) with (rav := reg_get regs 1) (s0v := reg_get regs 8) (s1v := reg_get regs 9)
      (s2v := reg_get regs 18) (s3v := reg_get regs 19) (j := j).
    - change (bv_unsigned (reg_get regs2 2)) with (spZ regs2). rewrite SP2.
      replace (spZ regs - 48) with (spZ regs + -48) by lia. exact SAV2.
    - change (bv_unsigned (reg_get regs2 2)) with (spZ regs2). rewrite SP2. lia.
    - exact BZ2. }
  intros ms' (can & PR & EQV).
  destruct PR as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->).
  destruct (rk_eqv_shape _ _ _ _ _ _ EQV) as (Ems & XR2).
  destruct (pn_final_regs regs regs2 (ms_regs ms') _ _ _ (reg_get regs2 10) _ _ _ _ _ _ _ _ _ _ _ XR2 ltac:(lia) GK2)
    as (RPF & R10F).
  assert (RPV : rpost B API PN_K L A regs mem md (parse_noting_writes out) (fun _ _ => False)
                  L1 A1 (ms_regs ms') mem2 md1).
  { apply (rk_seq PN_K L A regs mem md _ L A regs m1 md PJ_PARSE_K regs1 _ _ L1 A1 regs2 mem2 md1 (ms_regs ms')
             RPA RP2).
    - exact RPF.
    - rewrite S1. lia.
    - rewrite S1. lia.
    - exact HAC.
    - exact KP.
    - intros a _ _ He He2. apply He. exact He2.
    - intros a _ _ He He2. apply He. exact He2.
    - intros p n i _ _ _ He He2. apply He. exact He2.
    - intros p n _ _ HF. exact HF.
    - intros a Ha Hd. left. unfold scratch_k in Ha, Hd. rewrite S1 in Hd. unfold pj_parse_writes.
      intros [Ho|Hst]; [unfold hide in HDS2; lia | pose proof (STL a Hst); lia]. }
  rewrite Ems. apply SR_ret. unfold POST. cbv beta.
  exists fx2, L1, A1, (ms_regs ms'), mem2, md1, Lam1, peak1, cnt1, fail1, ok, res, tr.
  split.
  { change (reg_get regs 1) with (getr regs 1). rewrite (rk_ret_pc _ HRA). rewrite SEG. reflexivity. }
  split; [exact FRM2|]. split; [exact FK2|]. split; [exact RPV|].
  split; [exact RDC2|].
  split; [rewrite SEG; exact BZ2|].
  split; [exact LG2|].
  split; [exact JV|]. split; [exact OKS|]. split; [exact CNT1|]. split; [exact FA1|]. split; [exact PK1|].
  split; [exact HP1|]. split; [exact IMP1|]. split; [exact IMP2|].
  destruct res as [t|].
  - destruct ARM as (R102 & RF1 & D & PD & HELD & NLV & NB & PN).
    split; [rewrite R10F; exact R102|]. split; [exact RF1|].
    exists D. split; [exact PD|]. split; [exact HELD|]. split; [exact NLV|]. split; [exact NB|]. exact PN.
  - destruct ARM as (R102 & EXD & PERM & PZ).
    split; [rewrite R10F; exact R102|]. split; [exact EXD|]. split; [exact PERM|]. exact PZ.
Qed.

End KB.

Section Final.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable RF : ResForm.

(* fuzz_alloc_ran_out_reset_contract stays a premise although the #102 parse_noting no longer calls
   fuzz_alloc_ran_out_reset: the premise list is the old one, so lib/U/Prog/CF/LinkU.v's and LinkU34.v's lu_parse_noting
   need no edit. *)
Theorem parse_noting_holds :
  globals_free B API omx_G ->
  fuzz_alloc_live_c.fuzz_alloc_live_contract ->
  fuzz_alloc_ran_out_reset_c.fuzz_alloc_ran_out_reset_contract ->
  pj_parse_contract B API RF ->
  fuzz_alloc_ran_out_c.fuzz_alloc_ran_out_contract ->
  parse_noting_contract B API RF.
Proof.
  intros HG LIVEC _ PJ RANC. unfold parse_noting_contract.
  intros L A regs mem md Lam peak cnt fail b t0 len out tb ENV.
  exact (pn_main B API RF (proj1 ENV) HG LIVEC PJ RANC
           L A regs mem md Lam peak cnt fail b t0 len out tb ENV).
Qed.

End Final.
