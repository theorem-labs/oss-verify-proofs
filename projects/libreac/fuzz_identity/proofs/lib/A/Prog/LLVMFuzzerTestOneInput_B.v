(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_H.v, with its addresses and numbers changed; 496 of its 603 lines of code are new or changed and 1036 lines of the source are left out. *)
(* Segment B of LLVMFuzzerTestOneInput's ASan walk: the start-up checks, 0x8098c..0x80a7c (60 slots).
   seg_B of lib/A/Prog/LLVMFuzzerTestOneInput_inv.v: from inv_A_end (0x8098c) to inv_B_end, the slot of the
   memset call that clears `hw`.

   The code: 0x8098c x20 := x16 + 352 (&id); 0x80990 .. 0x809a4 the five shadow bytes of `id` (0, 0, 0, 0, 6);
   0x809b0 mf+184 := &id; then the eight calls, each followed by a test of a0 whose other branch jumps to the
   error block at 0x822f0:
     0x809ac reac_identity_init(NULL)          0x809b8 reac_identity_init(&id)
     0x809cc reac_identity_ingest(NULL,0,NULL,0) and 0x809ec reac_identity_ingest(&id,0,NULL,4): a0 = -1 (beq)
     0x80a04 reac_identity_fw_str(0,NULL,8): a0 < 0     0x80a24 reac_identity_reac_ver_str(0,0,0,NULL,20): a0 < 0
     0x80a44 reac_box_catalogue_defect(NULL,8,8,"x"): a0 = 0     0x80a50 reac_box_family_of(NULL): a0 = 0
   and 0x80a5c .. 0x80a78: a0 := mf+80 + 432 = &hw, mf+48 := &hw, a1 := 0, a2 := 12, the shadow bytes of `hw`
   (0 and 4).

   reac_identity_init(&id) is taken through its contract (HINIT). The seven calls with a NULL or empty argument
   are followed into the callee: each callee saves its registers in its own frame below sp, tests the argument at
   once, restores them and returns (-1 or 0) without a load or store outside that frame, apart from the second
   reac_identity_ingest call, which reads the shadow base through the image's two cells (objects 1 and 30) before
   its test. The engine runs these paths symbolically, so every test of a0 above is decided by the engine and the
   error block is never reached. (reac_identity_init's contract does not cover NULL: its tdst_ok premise asks that
   the 38 bytes at the argument lie in a heap block or a side-stack frame.) *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require reac_identity_init.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* The symbolic state at 0x8098c. Region 0: the 64 bytes below the machine frame that the callees' own frames
   use (base sp, atom 2). Region 1: the machine frame's slots mf+48 .. mf+192 (base s1, atom 9), written at
   mf+184 (0x809b0) and mf+48 (0x80a74); mf+80 holds the frame pointer (atom 16, a6) and mf+176 the shadow base.
   Region 2: the frame's shadow bytes 44 .. 55 (base s3, atom 19), written at 0x80990 .. 0x809a4 and
   0x80a68 / 0x80a6c. Atom 16 (the frame) is at least 4096, so the null tests on &id are decided. *)
Definition sb_stk : YP09.region := stack_region 64.
Definition sb_mf : YP09.region := YP09.mkRegion (Some 9%nat) 48 192 48 192
  [YP09.mkChunk 80 (CVal 8 (SOff 16 0)); YP09.mkChunk 176 (CVal 8 (SLit 0x7fff8000))].
Definition sb_sh : YP09.region := YP09.mkRegion (Some 19%nat) 44 56 44 56 [].
Definition sb_facts : facts := mkFacts [(16%nat, mkAF 4096 (2 ^ 47) 0)] [] [].
Definition ss_b : sstate := mkSS 0x280 sr_atoms [sb_stk; sb_mf; sb_sh] None sb_facts.
(* The writable windows of the walk's states (the image cells of phase 2 are read-only). *)
Definition sb_win (mf sh a : Z) : Prop := (mf - 64 <= a < mf) \/ (mf + 48 <= a < mf + 192) \/ (sh + 44 <= a < sh + 56).
Definition sb_ws : list (option nat * Z * Z) :=
  [(Some (A_OBJ 30), 0, 0); (Some (A_OBJ 1), 0, 0); (Some 2%nat, -64, 0); (Some 9%nat, 48, 192); (Some 19%nat, 44, 56)].

Lemma sb_ws_ok : forall E mf sh, bv_unsigned (ew E 2) = mf -> bv_unsigned (ew E 9) = mf -> bv_unsigned (ew E 19) = sh ->
  forall b wlo whi a, In (b, wlo, whi) sb_ws -> base_val E b + wlo <= a < base_val E b + whi -> sb_win mf sh a.
Proof.
intros E mf sh U2 U9 U19 b wlo whi a Hin Ha. unfold sb_ws in Hin. cbn [In] in Hin. unfold sb_win.
destruct Hin as [Eq | [Eq | [Eq | [Eq | [Eq | []]]]]]; injection Eq as <- <- <-; cbn [base_val] in Ha;
[lia | lia | rewrite U2 in Ha; lia | rewrite U9 in Ha; lia | rewrite U19 in Ha; lia].
Qed.
Lemma sb_ws1_ok : forall E mf sh, bv_unsigned (ew E 2) = mf -> bv_unsigned (ew E 9) = mf -> bv_unsigned (ew E 19) = sh ->
  forall b wlo whi a, In (b, wlo, whi) (skipn 2 sb_ws) -> base_val E b + wlo <= a < base_val E b + whi -> sb_win mf sh a.
Proof.
intros E mf sh U2 U9 U19 b wlo whi a Hin Ha. apply (sb_ws_ok E mf sh U2 U9 U19 b wlo whi a); [|exact Ha].
unfold sb_ws in *. cbn [skipn In] in *. tauto.
Qed.

Section h.
Variable segs : list Segment.
Lemma sb_kept : forall E rs H (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> forall ws (Zs : Z -> Prop), windows rs = ws ->
  (forall b wlo whi a, In (b, wlo, whi) ws -> base_val E b + wlo <= a < base_val E b + whi -> Zs a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs H m' a = aview segs H m a.
Proof. intros E rs H m m' HF ws Zs Hw HZ. subst ws. exact (kept_of_frame E rs H m m' Zs HF HZ). Qed.
Lemma sb_trans : forall (Zs : Z -> Prop) (f g h : Z -> option Z),
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> g a = f a) -> (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> h a = g a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> h a = f a.
Proof. intros Zs f g h H1 H2 a Ha Hz. rewrite (H2 a Ha Hz). exact (H1 a Ha Hz). Qed.
End h.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).

(* A program call the walk follows into the callee: the engine stopped at the call with the pc at the callee's
   first slot BASE + af, and the run goes on there. *)
Lemma sb_enter : forall E ss k ms,
  st_ok SEGS E (setpc ss (BASE + k)) ms -> st_ok_pi SEGS VAL E (setpc ss k) ms.
Proof. intros E ss k ms H. exact H. Qed.
Lemma sb_awr : forall E rs ws STK sp0 FP bl0 blc ly own (Zs : Z -> Prop),
  windows rs = ws ->
  (forall b wlo whi a, In (b, wlo, whi) ws -> base_val E b + wlo <= a < base_val E b + whi -> Zs a) ->
  (forall a, Zs a -> awr_byte STK sp0 FP bl0 blc ly own a) ->
  awr_ok E rs STK sp0 FP bl0 blc ly own.
Proof.
intros E rs ws STK sp0 FP bl0 blc ly own Zs Hw HZ HA a Ha. apply HA.
destruct (in_wrange_windows E rs a Ha) as (b & wlo & whi & Hi & Hr). subst ws. exact (HZ b wlo whi a Hi Hr).
Qed.
(* A one-byte chunk of a region holds its literal. *)
Lemma sb_cell_of : forall E H (m : word -> option byte) base cs off v,
  Forall (YP09.chunk_ok SEGS E (mrestrict H m) base) cs ->
  In (YP09.mkChunk off (CVal 1 (SLit v))) cs -> 0 <= v < 256 -> aview SEGS H m (base + off) = Some v.
Proof.
intros E H m base cs off v Hcs Hin Hv.
destruct (proj1 (Forall_forall _ _) Hcs _ Hin 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
cbn [YP09.c_off YP09.c_val cbyte sv_denot] in Hb1, Hb2. injection Hb1 as <-.
rewrite Z.add_0_r in Hb2. unfold aview. rewrite Hb2. cbn [option_map]. f_equal.
unfold YP09.byte_of_word. rewrite unsigned_lit_small by lia. rewrite Z.mul_0_r, Z.shiftr_0_r.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. exact Hv.
Qed.
(* A region whose bytes a call kept, across a change of world. *)
Lemma sb_region_kept : forall E H H' (m m2 : word -> option byte) n b lo hi wlo whi cs,
  bv_unsigned (ew E n) = b ->
  (forall a, b + lo <= a < b + hi -> aview SEGS H' m2 a = aview SEGS H m a) ->
  (forall a, b + wlo <= a < b + whi -> apresent H' m2 a) ->
  region_kept SEGS E (mrestrict H m) (mrestrict H' m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H H' m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.
Lemma sb_val_mem1 : forall H mem a v, aview SEGS H mem a = Some v -> val_mem SEGS (mrestrict H mem) a 1 v.
Proof.
intros H mem a v Hv j Hj. assert (j = 0%nat) by lia. subst j. rewrite Z.add_0_r.
destruct (aview_byte SEGS H mem a v Hv) as (b & Hb & -> & Hr). rewrite Hb. f_equal.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, YO0f.le_byte. change (bv_modulus 8) with 256.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
rewrite !(Z.mod_small (bv_unsigned b) 256 Hr). reflexivity.
Qed.
Lemma sb_garr8_moved : forall H H' (m m' : word -> option byte) a l,
  (forall k, 0 <= k < Z.of_nat (length l) -> aview SEGS H' m' (a + k) = aview SEGS H m (a + k)) ->
  garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved SEGS H H' m m' (a + Z.of_nat j) (a + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros k Hk1. replace (a + Z.of_nat j + k) with (a + (Z.of_nat j + k)) by lia. apply Hk. lia.
Qed.
(* The shadow of `id` (38 bytes at F + 352) as 0x80990 .. 0x809a4 set it: four 0 cells and a last cell 6. *)
Lemma sb_id_shadow : forall (rd : Z -> option Z) F, F mod 64 = 0 ->
  rd (SHADOW_OFF + F / 8 + 44) = Some 0 -> rd (SHADOW_OFF + F / 8 + 45) = Some 0 ->
  rd (SHADOW_OFF + F / 8 + 46) = Some 0 -> rd (SHADOW_OFF + F / 8 + 47) = Some 0 ->
  rd (SHADOW_OFF + F / 8 + 48) = Some 6 ->
  block_shadow rd SHADOW_OFF (F + 352) 38 /\ zero_shadow rd SHADOW_OFF (F + 352) 38.
Proof.
intros rd F HF H0 H1 H2 H3 H4.
assert (Es : shadow_of_addr SHADOW_OFF (F + 352) = SHADOW_OFF + F / 8 + 44) by (unfold shadow_of_addr; lia).
split.
- split; [lia|]. split; [lia|]. intros i Hi. rewrite Es. change ((38 + 7) / 8) with 5 in Hi.
  assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | ->]]]];
  [ rewrite Z.add_0_r; exact H0
  | replace (SHADOW_OFF + F / 8 + 44 + 1) with (SHADOW_OFF + F / 8 + 45) by lia; exact H1
  | replace (SHADOW_OFF + F / 8 + 44 + 2) with (SHADOW_OFF + F / 8 + 46) by lia; exact H2
  | replace (SHADOW_OFF + F / 8 + 44 + 3) with (SHADOW_OFF + F / 8 + 47) by lia; exact H3
  | replace (SHADOW_OFF + F / 8 + 44 + 4) with (SHADOW_OFF + F / 8 + 48) by lia; exact H4 ].
- intros i Hi. rewrite Es. change (38 / 8) with 4 in Hi.
  assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
  destruct Hc as [-> | [-> | [-> | ->]]];
  [ rewrite Z.add_0_r; exact H0
  | replace (SHADOW_OFF + F / 8 + 44 + 1) with (SHADOW_OFF + F / 8 + 45) by lia; exact H1
  | replace (SHADOW_OFF + F / 8 + 44 + 2) with (SHADOW_OFF + F / 8 + 46) by lia; exact H2
  | replace (SHADOW_OFF + F / 8 + 44 + 3) with (SHADOW_OFF + F / 8 + 47) by lia; exact H3 ].
Qed.
(* The shadow hull of `id` is cells 40 .. 55 of the frame's shadow. *)
Lemma sb_id_hull : forall F s, F mod 64 = 0 -> 0 <= F ->
  shadow_addr (F + 352) / 8 * 8 <= s < shadow_addr (F + 352 + 38 - 1) / 8 * 8 + 8 ->
  shadow_addr F + 40 <= s < shadow_addr F + 56.
Proof. intros F s HF H0 Hs. unfold shadow_addr, SHADOW_OFF in *. lia. Qed.

Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section of LLVMFuzzerTestOneInput.v / _inv.v, in the same order. *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
(* What this segment needs, each as LLVMFuzzerTestOneInput.v's Section states it, in its order. *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis PSIG : ident_prog_sig_ok (PI := PI).
Hypothesis MTL : ameter_laws MT.
Hypothesis HMT0 : forall s s' : astate, mo_le MT s s' 0.
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Hypothesis HINIT : reac_identity_init.treac_identity_init_spec B (BASE + AF_reac_identity_init).
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
(* After a run: what it kept outside the windows, chained onto KP; the run's frame facts are then dropped. *)
Ltac sb_keep KP WOK Zs :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    let K := fresh "K" in
    pose proof (sb_kept SEGS _ _ _ _ _ HFr sb_ws Zs ltac:(vm_compute; reflexivity) WOK) as K;
    let KP' := fresh "KP" in pose proof (sb_trans _ _ _ _ KP K) as KP'; clear KP K; rename KP' into KP end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* One run of phase 2 that ends at a program call. *)
Ltac sb_go RUNP RUNC HS HJ AW WOK KP Zs :=
  paj_run_shc RUNP RUNC HS HJ;
  [ apply (sb_awr _ _ sb_ws _ _ _ _ _ _ _ Zs); [vm_compute; reflexivity | exact WOK | exact AW] | ];
  sb_keep KP WOK Zs.
Ltac sb_nss HS := lazymatch type of HS with st_ok_pi ?a ?b ?c ?s ?d =>
  let v := eval vm_compute in s in change (st_ok_pi a b c v d) in HS end.
Ltac sb_in := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac sb_disj U2h U9h U19h Eo1h Eo30h HgotV HcellV Hsh0 Hsh1 Hmf0 HgotR HcellR HgcD :=
  apply all_disjoint_of_extents; unfold extent_of_region;
  cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi base_val zall_disjoint sb_stk stack_region got_regionP bcell_regionP
       A_OBJ Nat.add];
  rewrite ?U2h, ?U9h, ?U19h, ?Eo1h, ?Eo30h, ?unsigned_lit_small by (clear - HgotV HcellV; lia);
  cbn [zall_disjoint]; unfold zdisj; cbn [fst snd];
  repeat split; clear - Hsh0 Hsh1 Hmf0 HgotR HcellR HgcD; lia.

Theorem seg_B_holds :
  seg_B B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
    arodata_okS.
Proof.
intros g pos mf W2 c2 Hstart.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & Rs3 & V80 & V192 & V176 & Vra & Vs0 &
  V24 & V32 & V40 & V48 & V56 & V64 & V72 & V80b & V88 & V96 & V104 & Vmf24 & Vflag & HPRE & Hfds & Hfs & Hinb).
destruct HP as (P0 & P8 & P16 & P1016 & Hbl & R16 & R18 & R26).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
pose proof HPRE as (HFN & Hraz & _ & _ & Hinp & Hlen & _ & _ & Hnev0 & _).
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & Hnev2 & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _ & _ & ETop & _).
set (sp0 := e_sp0 g) in *.
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
set (SF := SFa g pos) in *.
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF0 & HSF1 & HSFapp).
destruct (frame_al64 SEGS B ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF64 & _ & _).
rewrite EFa in HSF0, HSF1, HSFapp, HSF64. rewrite HFB in HSF1, HSFapp.
set (sh := shadow_addr SF) in *.
assert (Esh : sh = SHADOW_OFF + SF / 8) by reflexivity.
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
assert (Hsh1 : 0 <= sh /\ sh + 128 <= alloc_ceiling).
{ clear - Esh HSF0 HSF1 C1. clearbody sh SF. unfold SHADOW_OFF in Esh. lia. }
assert (Hsh0 : 0x7fff8000 <= sh) by (rewrite Esh; unfold SHADOW_OFF; clear - HSF0; lia).
(* the environment: atoms 0 .. 31 the registers at 0x8098c, atom 32 the shadow base *)
remember (Eimg (Ereg regs2 [Z_to_bv 64 SHADOW_OFF])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (ER : regs_ok E sr_atoms regs2) by (rewrite HE; apply regs_ok_Eimg_Ereg).
assert (Eo1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
  by (rewrite HE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo30 : ew E (A_OBJ 30) = Z_to_bv 64 (VAL (A_OBJ 30)))
  by (rewrite HE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
clear HE.
assert (U2 : bv_unsigned (ew E 2) = mf).
{ rewrite (EE 2%nat 2%bv eq_refl), Rsp. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite (EE 9%nat 9%bv eq_refl), Rs1. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
assert (U19 : bv_unsigned (ew E 19) = sh).
{ rewrite (EE 19%nat 19%bv eq_refl), Rs3. apply unsigned_lit_small. clear - Hsh1 C1. lia. }
assert (E16 : ew E 16 = Z_to_bv 64 SF) by (rewrite (EE 16%nat 16%bv eq_refl), R16; reflexivity).
assert (HS : st_ok_pi SEGS VAL E ss_b
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x280)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_b. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor; [|constructor]]].
    + unfold sb_stk, stack_region, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U2. split; [clear - Hmf0 C1; lia|]. split; [clear - Hmf0 H47 Hmfb Hshi; unfold sp0 in *; lia|].
      split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      apply (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
        [(4, pos)] ly2 S2 W2 mem2 md2 0 (mf + o) HJ ltac:(left; clear - Ho Hmfb HSTK' Has; lia))).
    + unfold sb_mf, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [clear - Hmf0 C1; lia|]. split; [clear - Hmf0 H47 Hmfb Hshi; unfold sp0 in *; lia|].
      split.
      { intros o Ho. apply (apresent_writable SEGS).
        apply (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
          [(4, pos)] ly2 S2 W2 mem2 md2 0 (mf + o) HJ ltac:(left; clear - Ho Hmfb HSTK' Has; lia))). }
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val SEGS E _ mf 80 8 (SOff 16 0) SF);
        [cbn [sv_denot]; rewrite E16, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - HSF0 HSF1 C1; lia | lia | exact V80].
      * apply (chunk_ok_val SEGS E _ mf 176 8 (SLit 0x7fff8000) SHADOW_OFF);
        [reflexivity | unfold SHADOW_OFF; lia | lia | exact V176].
    + unfold sb_sh, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U19. split; [clear - Hsh1; lia|]. split; [clear - Hsh1 C1; lia|].
      split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      apply (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
        [(4, pos)] ly2 S2 W2 mem2 md2 0 (sh + o) HJ ltac:(
        right; right; right; exists 4, pos; split; [left; reflexivity|]; right;
        unfold in_zr; cbn [fst snd]; rewrite EFa, HFB; fold sh; clear - Ho; lia))).
  - apply pairwise_disjoint_of_extents. unfold sb_stk, stack_region, sb_mf, sb_sh, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U9, U19.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; clear - Hsh1 Hmf0; lia.
  - unfold facts_ok, sb_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; exact I]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E16, unsigned_lit_small by (clear - HSF0 HSF1 C1; lia).
    rewrite Z.pow_0_r, Z.mod_1_r. clear - HSF0 HSF1 C1. lia. }
(* the windows every run of the walk may write, and the caller's right to write them *)
assert (AWR1 : forall a, sb_win mf sh a ->
  awr_byte LLVMF_STK sp0 [] (ablocks B (e_ly g) (e_S g)) (ablocks B ly2 S2) ly2 [(4, pos)] a).
{ intros a [Ha | [Ha | Ha]].
  - left. clear - Ha Hmfb HSTK' Has. lia.
  - left. clear - Ha Hmfb HSTK' Has. lia.
  - right; right; right. exists 4, pos. split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite EFa, HFB. fold sh. clear - Ha. lia. }
unfold cfg_at. change (w64 (BASE + 0x280)) with (Z_to_bv 64 (BASE + 0x280)).
(* ---- run 1: 0x8098c .. the call of reac_identity_init(NULL) at 0x809ac ---- *)
paj_run_shc RUNP RUNC HS HJ.
{ apply (sb_awr E _ (skipn 2 sb_ws) _ _ _ _ _ _ _ (sb_win mf sh)); [vm_compute; reflexivity | | exact AWR1].
  exact (sb_ws1_ok E mf sh U2 U9 U19). }
pose proof (sb_kept SEGS _ _ _ _ _ HFr (skipn 2 sb_ws) (sb_win mf sh) ltac:(vm_compute; reflexivity) (sb_ws1_ok E mf sh U2 U9 U19))
  as K1.
clear HF HFr HG.
rewrite (PSIG IS_reac_identity_init AF_reac_identity_init eq_refl) in HS. apply sb_enter in HS.
(* ---- run 2: reac_identity_init(NULL) returns at once (0x838e0 beqz a0); 0x809b0 .. the call at 0x809b8 ---- *)
paj_run_shc RUNP RUNC HS HJ.
{ apply (sb_awr E _ (skipn 2 sb_ws) _ _ _ _ _ _ _ (sb_win mf sh)); [vm_compute; reflexivity | | exact AWR1].
  exact (sb_ws1_ok E mf sh U2 U9 U19). }
pose proof (sb_kept SEGS _ _ _ _ _ HFr (skipn 2 sb_ws) (sb_win mf sh) ltac:(vm_compute; reflexivity) (sb_ws1_ok E mf sh U2 U9 U19))
  as K2.
clear HF HFr HG.
pose proof (sb_trans _ _ _ _ K1 K2) as KP1. clear K1 K2.
(* ---- the call reac_identity_init(&id) at 0x809b8, through its contract (HINIT) ---- *)
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10.
rewrite (EE 2%nat 2%bv eq_refl), Rsp in Q2. rewrite (EE 3%nat 3%bv eq_refl), Rgp in Q3.
rewrite (EE 4%nat 4%bv eq_refl), Rtp in Q4.
assert (Q10' : getr (ms_regs ms0) 10 = w64 (SF + V_id)).
{ rewrite Q10. unfold w64, V_id. rewrite E16, unsigned_lit_small by (clear - HSF0 HSF1 C1; lia). reflexivity. }
assert (Usp : spZ (ms_regs ms0) = mf).
{ unfold spZ. rewrite Q2. unfold w64. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
pose proof HJ as (HARc & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos HARc Hin4) as (_ & _ & _ & HFSc).
rewrite EFa, HFB in HFSc. fold sh in HFSc.
(* the shadow of `id` as 0x80990 .. 0x809a4 wrote it *)
pose proof (st_ok_region_nth E _ _ 2 _ HS eq_refl) as HRsh.
destruct HRsh as (_ & _ & _ & Hcs). cbn [YP09.r_chunks YP09.r_base base_val ms_mem restrict] in Hcs. rewrite U19 in Hcs.
assert (S44 : aview SEGS (w_H W2) (ms_mem ms0) (SHADOW_OFF + SF / 8 + 44) = Some 0)
  by (rewrite <- Esh; apply (sb_cell_of E _ _ sh _ 44 0 Hcs); [sb_in | clear - HSF0; lia]).
assert (S45 : aview SEGS (w_H W2) (ms_mem ms0) (SHADOW_OFF + SF / 8 + 45) = Some 0)
  by (rewrite <- Esh; apply (sb_cell_of E _ _ sh _ 45 0 Hcs); [sb_in | clear - HSF0; lia]).
assert (S46 : aview SEGS (w_H W2) (ms_mem ms0) (SHADOW_OFF + SF / 8 + 46) = Some 0)
  by (rewrite <- Esh; apply (sb_cell_of E _ _ sh _ 46 0 Hcs); [sb_in | clear - HSF0; lia]).
assert (S47 : aview SEGS (w_H W2) (ms_mem ms0) (SHADOW_OFF + SF / 8 + 47) = Some 0)
  by (rewrite <- Esh; apply (sb_cell_of E _ _ sh _ 47 0 Hcs); [sb_in | clear - HSF0; lia]).
assert (S48 : aview SEGS (w_H W2) (ms_mem ms0) (SHADOW_OFF + SF / 8 + 48) = Some 6)
  by (rewrite <- Esh; apply (sb_cell_of E _ _ sh _ 48 6 Hcs); [sb_in | clear - HSF0; lia]).
destruct (sb_id_shadow (aview SEGS (w_H W2) (ms_mem ms0)) SF HSF64 S44 S45 S46 S47 S48) as [BS0 _].
clear Hcs S44 S45 S46 S47 S48.
pmkst HS.
rewrite (PSIG IS_reac_identity_init AF_reac_identity_init eq_refl).
eapply SRr_bind.
{ apply (HINIT LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 W2 (ms_mem ms0) _ 0
    (ms_regs ms0) (SF + V_id) HJ).
  - rewrite Q1. apply ret_ok_codeptr_v; [clear - HSF0; lia | reflexivity].
  - exact Q3.
  - exact Q4.
  - exact Q10'.
  - rewrite Usp. clear - Hmf32. lia.
  - rewrite Usp. unfold reac_identity_init.REAC_IDENTITY_INIT_STK, ESTACK. clear - Hmfb HSTK' Has. lia.
  - rewrite Usp. clear - Hmfb. lia.
  - intros a Ha. right. exists 4, pos. split; [exact Hin4|]. unfold in_zr, frame_rng. cbn [fst snd].
    rewrite EFa, HFB. unfold reac_identity_init.IDENT_SIZE, V_id in Ha. clear - Ha. lia.
  - intros a Ha. unfold reac_identity_init.IDENT_SIZE, V_id in Ha.
    assert (Haw : awr_byte LLVMF_STK sp0 [] (ablocks B (e_ly g) (e_S g)) (ablocks B ly2 S2) ly2 [(4, pos)] a).
    { right; right; right. exists 4, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
      rewrite EFa, HFB. clear - Ha. lia. }
    destruct (awr_byte_present SEGS B LAWS LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
      ly2 S2 W2 (ms_mem ms0) _ 0 a HJ Haw) as [Hp Ho].
    split; [exact Haw|]. split; [exact Hp|]. split; [exact Ho|].
    rewrite Usp. unfold ESTACK. clear - Ha HSF1 Hmf0. lia.
  - unfold V_id, reac_identity_init.IDENT_SIZE. apply (block_shadow_range _ _ (SF + 352) 38); [exact BS0 | clear - HSF0; lia | clear - HSF0; lia].
  - intros s Hs. unfold V_id, reac_identity_init.IDENT_SIZE in Hs.
    pose proof (sb_id_hull SF s HSF64 ltac:(clear - HSF0; lia) Hs) as Hs'. fold sh in Hs'.
    apply (aview_some_of_apresent SEGS). replace s with (sh + (s - sh)) by (clear - Hs'; lia).
    apply (proj1 (HFSc (s - sh) ltac:(clear - Hs'; lia))). }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hfr3 & Hperm3 & Hzero3 & Hkept3).
rewrite Q1.
pose proof HJ3 as (HAR3 & Hly3 & _).
pose proof Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
assert (EFa3 : frame_addr ly3 4 pos = SF) by (unfold SF, SFa, frame_addr; rewrite EF3; reflexivity).
destruct Hkept3 as (KK1 & KK2 & _ & KK4 & _ & _). rewrite Usp in KK1.
(* back at 0x809bc: the machine-frame slots and the frame's shadow survive the call *)
jafter_call_keep_hi HS 512%nat regs3 (mrestrict (w_H W3) mem3) HP3 [1%nat; 2%nat] HS3.
match type of HS3 with ?Q -> _ => assert (HQ : Q); [|specialize (HS3 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. constructor; [|constructor; [|constructor]].
  - apply (sb_region_kept E (w_H W2) (w_H W3) (ms_mem ms0) mem3 9 mf); [exact U9 | |].
    + intros a Ha. apply KK1; [clear - Ha Hmf0 Hmfb H47 Hshi C1; lia | clear - Ha; lia |].
      cbv beta. unfold V_id, reac_identity_init.IDENT_SIZE. clear - Ha HSF1 Hmf0. lia.
    + intros a Ha. exact (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g)
        (e_md g) [(4, pos)] ly3 S3 W3 mem3 md3 0 a HJ3 ltac:(left; clear - Ha Hmfb HSTK' Has; lia))).
  - apply (sb_region_kept E (w_H W2) (w_H W3) (ms_mem ms0) mem3 19 sh); [exact U19 | |].
    + intros a Ha. apply (KK4 4 pos a Hin4).
      * right. unfold in_zr. cbn [fst snd]. rewrite EFa, HFB. fold sh. clear - Ha. lia.
      * cbv beta. unfold V_id, reac_identity_init.IDENT_SIZE. intros Hin.
        apply (fshadow_not_app SF 128 SF 1024 a); [exact HSF0 | clear - HSF1 C1; lia | exact HSFapp | | clear - Hin; lia].
        rewrite Esh in Ha. unfold SHADOW_OFF in Ha. clear - Ha. lia.
    + intros a Ha. exact (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g)
        (e_md g) [(4, pos)] ly3 S3 W3 mem3 md3 0 a HJ3 ltac:(
        right; right; right; exists 4, pos; split; [left; reflexivity|]; right;
        unfold in_zr; cbn [fst snd]; rewrite EFa3, HFB; fold sh; clear - Ha; lia))). }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
pose proof (img_env_havoc_hi E 512%nat (map (getr regs3) CLOB) HEI (le_n 512)) as HEI3.
assert (EH : forall n, (n < 512)%nat -> ew (havoc E 512 (map (getr regs3) CLOB)) n = ew E n)
  by (intros n Hn; apply ew_havoc_old; exact Hn).
assert (U2h : bv_unsigned (ew (havoc E 512 (map (getr regs3) CLOB)) 2) = mf) by (rewrite EH by (clear - EH; lia); exact U2).
assert (U9h : bv_unsigned (ew (havoc E 512 (map (getr regs3) CLOB)) 9) = mf) by (rewrite EH by (clear - EH; lia); exact U9).
assert (U19h : bv_unsigned (ew (havoc E 512 (map (getr regs3) CLOB)) 19) = sh) by (rewrite EH by (clear - EH; lia); exact U19).
assert (E16h : ew (havoc E 512 (map (getr regs3) CLOB)) 16 = Z_to_bv 64 SF) by (rewrite EH by (clear - EH; lia); exact E16).
assert (E32h : ew (havoc E 512 (map (getr regs3) CLOB)) 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EH by (clear - EH; lia); exact E32).
assert (Eo1h : ew (havoc E 512 (map (getr regs3) CLOB)) 242 = Z_to_bv 64 (VAL (A_OBJ 1)))
  by (rewrite EH by (clear - EH; lia); exact Eo1).
assert (Eo30h : ew (havoc E 512 (map (getr regs3) CLOB)) 271 = Z_to_bv 64 (VAL (A_OBJ 30)))
  by (rewrite EH by (clear - EH; lia); exact Eo30).
(* the regions phase 2 adds: the callees' frames below sp again, and the two image cells reac_identity_ingest reads *)
destruct (al_const _ _ LAWS _ _ _ _ _ HAR3) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 1 (proj1 (Nat.ltb_lt 1 31) eq_refl)) as HgotR.
pose proof (pa_obj_img 30 (proj1 (Nat.ltb_lt 30 31) eq_refl)) as HcellR.
pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_val_range (A_OBJ 1)) as HgotV. pose proof (pa_val_range (A_OBJ 30)) as HcellV.
assert (RSTK : region_ok SEGS (havoc E 512 (map (getr regs3) CLOB)) (mrestrict (w_H W3) mem3) sb_stk).
{ unfold sb_stk, stack_region, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U2h. split; [clear - Hmf0 C1; lia|]. split; [clear - Hmf0 H47 Hmfb Hshi; unfold sp0 in *; lia|].
  split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS).
  exact (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
    [(4, pos)] ly3 S3 W3 mem3 md3 0 (mf + o) HJ3 ltac:(left; clear - Ho Hmfb HSTK' Has; lia))). }
assert (RGOT : region_ok SEGS (havoc E 512 (map (getr regs3) CLOB)) (mrestrict (w_H W3) mem3) got_regionP).
{ unfold region_ok, got_regionP. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  change (A_OBJ 1) with 242%nat. rewrite Eo1h, unsigned_lit_small by (clear - HgotV; lia).
  split; [clear - HgotV; lia|]. split; [clear - HgotR; lia|]. split; [intros oo Hoo; clear - Hoo; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS _ _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 30) 0) (VAL (A_OBJ 30)));
  [ cbn [sv_denot]; change (A_OBJ 30) with 271%nat; rewrite Eo30h, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - HcellV; lia | exact (Z.le_refl 8) |].
  rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot). }
assert (RBC : region_ok SEGS (havoc E 512 (map (getr regs3) CLOB)) (mrestrict (w_H W3) mem3) (bcell_regionP 32)).
{ unfold region_ok, bcell_regionP. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  change (A_OBJ 30) with 271%nat. rewrite Eo30h, unsigned_lit_small by (clear - HcellV; lia).
  split; [clear - HcellV; lia|]. split; [clear - HcellR; lia|]. split; [intros oo Hoo; clear - Hoo; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS _ _ (VAL (A_OBJ 30)) 0 8 (SOff 32 0) SHADOW_OFF);
  [ cbn [sv_denot]; rewrite E32h, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | unfold SHADOW_OFF; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear; lia | exact (Z.le_refl 8) |].
  rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell). }
pose proof (st_ok_pi_add_region _ _ _ sb_stk HS eq_refl RSTK ltac:(sb_disj U2h U9h U19h Eo1h Eo30h HgotV HcellV Hsh0 Hsh1 Hmf0 HgotR HcellR HgcD)) as HS'.
clear HS. rename HS' into HS. sb_nss HS.
pose proof (st_ok_pi_add_region _ _ _ got_regionP HS eq_refl RGOT ltac:(sb_disj U2h U9h U19h Eo1h Eo30h HgotV HcellV Hsh0 Hsh1 Hmf0 HgotR HcellR HgcD)) as HS'.
clear HS. rename HS' into HS. sb_nss HS.
pose proof (st_ok_pi_add_region _ _ _ (bcell_regionP 32) HS eq_refl RBC ltac:(sb_disj U2h U9h U19h Eo1h Eo30h HgotV HcellV Hsh0 Hsh1 Hmf0 HgotR HcellR HgcD)) as HS'.
clear HS. rename HS' into HS. sb_nss HS.
assert (AWR3 : forall a, sb_win mf sh a ->
  awr_byte LLVMF_STK sp0 [] (ablocks B (e_ly g) (e_S g)) (ablocks B ly3 S3) ly3 [(4, pos)] a).
{ intros a [Ha | [Ha | Ha]].
  - left. clear - Ha Hmfb HSTK' Has. lia.
  - left. clear - Ha Hmfb HSTK' Has. lia.
  - right; right; right. exists 4, pos. split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite EFa3, HFB. fold sh. clear - Ha. lia. }
pose proof (sb_ws_ok _ mf sh U2h U9h U19h) as WOK2.
assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ sb_win mf sh a ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W3) mem3 a) by (intros; reflexivity).
(* ---- run 3: 0x809bc .. the call reac_identity_ingest(NULL, 0, NULL, 0) at 0x809cc ---- *)
sb_go RUNP RUNC HS HJ3 AWR3 WOK2 KP (sb_win mf sh).
rewrite (PSIG IS_reac_identity_ingest AF_reac_identity_ingest eq_refl) in HS. apply sb_enter in HS.
(* ---- run 4: the refused call returns -1 at once (0x83910 beqz a0); 0x809d0 beq taken; .. the call
   reac_identity_ingest(&id, 0, NULL, 4) at 0x809ec ---- *)
sb_go RUNP RUNC HS HJ3 AWR3 WOK2 KP (sb_win mf sh).
rewrite (PSIG IS_reac_identity_ingest AF_reac_identity_ingest eq_refl) in HS. apply sb_enter in HS.
(* ---- run 5: refused (no payload for a length of 4, 0x83924 bnez a3), -1; 0x809f0 beq taken; .. the call
   reac_identity_fw_str(0, NULL, 8) at 0x80a04 ---- *)
sb_go RUNP RUNC HS HJ3 AWR3 WOK2 KP (sb_win mf sh).
rewrite (PSIG IS_reac_identity_fw_str AF_reac_identity_fw_str eq_refl) in HS. apply sb_enter in HS.
(* ---- run 6: no buffer (0x83e40 beqz a1), -1; 0x80a08 bltz taken; .. the call
   reac_identity_reac_ver_str(0, 0, 0, NULL, 20) at 0x80a24 ---- *)
sb_go RUNP RUNC HS HJ3 AWR3 WOK2 KP (sb_win mf sh).
rewrite (PSIG IS_reac_identity_reac_ver_str AF_reac_identity_reac_ver_str eq_refl) in HS. apply sb_enter in HS.
(* ---- run 7: no buffer (0x8406c beqz a3), -1; 0x80a28 bltz taken; .. the call
   reac_box_catalogue_defect(NULL, 8, 8, "x") at 0x80a44 ---- *)
sb_go RUNP RUNC HS HJ3 AWR3 WOK2 KP (sb_win mf sh).
rewrite (PSIG IS_reac_box_catalogue_defect AF_reac_box_catalogue_defect eq_refl) in HS. apply sb_enter in HS.
(* ---- run 8: no entry (0x837bc beqz a0), 0; 0x80a48 beqz taken; .. the call reac_box_family_of(NULL) at 0x80a50 ---- *)
sb_go RUNP RUNC HS HJ3 AWR3 WOK2 KP (sb_win mf sh).
rewrite (PSIG IS_reac_box_family_of AF_reac_box_family_of eq_refl) in HS. apply sb_enter in HS.
(* ---- run 9: no box (0x828fc beqz a0), 0; 0x80a54 beqz taken; 0x80a5c .. 0x80a78, to the memset call's slot ---- *)
paj_run_to_sh RUNTOP HS HJ3 0x370.
{ apply (sb_awr _ _ sb_ws _ _ _ _ _ _ _ (sb_win mf sh)); [vm_compute; reflexivity | exact WOK2 | exact AWR3]. }
sb_keep KP WOK2 (sb_win mf sh).
lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msE end.
(* ---- the boundary inv_B_end at 0x80a7c ---- *)
(* the registers *)
prreg HS (2%bv : bv 5) F2. prreg HS (9%bv : bv 5) F9. prreg HS (8%bv : bv 5) F8. prreg HS (3%bv : bv 5) F3.
prreg HS (4%bv : bv 5) F4. prreg HS (19%bv : bv 5) F19. prreg HS (10%bv : bv 5) F10. prreg HS (11%bv : bv 5) F11.
prreg HS (12%bv : bv 5) F12. prreg HS (18%bv : bv 5) F18. prreg HS (26%bv : bv 5) F26.
rewrite (EE 2%nat 2%bv eq_refl), Rsp in F2. rewrite (EE 9%nat 9%bv eq_refl), Rs1 in F9.
rewrite (EE 8%nat 8%bv eq_refl), Rs0 in F8. rewrite (EE 3%nat 3%bv eq_refl), Rgp in F3.
rewrite (EE 4%nat 4%bv eq_refl), Rtp in F4. rewrite (EE 19%nat 19%bv eq_refl), Rs3 in F19.
rewrite (EE 18%nat 18%bv eq_refl), R18 in F18. rewrite (EE 26%nat 26%bv eq_refl), R26 in F26.
assert (F10' : getr (ms_regs msE) 10 = w64 (SF + V_hw)).
{ rewrite F10. unfold w64, V_hw. rewrite E16, unsigned_lit_small by (clear - HSF0 HSF1 C1; lia). reflexivity. }
(* the machine-frame slots and the shadow cells the walk wrote *)
pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as HRmf.
pose proof (st_ok_pi_region_nth _ _ _ 4 _ HS eq_refl) as HRsh.
cbn [ms_mem restrict] in HRmf, HRsh.
pose proof (field_of_region_any _ _ 9%nat mf _ _ _ _ _ 184 8%N (SOff 16 352) HRmf U9h ltac:(sb_in) (Z.le_refl 8)) as M184.
pose proof (field_of_region_any _ _ 9%nat mf _ _ _ _ _ 48 8%N (SOff 16 432) HRmf U9h ltac:(sb_in) (Z.le_refl 8)) as M48.
pose proof (field_of_region_any _ _ 9%nat mf _ _ _ _ _ 80 8%N (SOff 16 0) HRmf U9h ltac:(sb_in) (Z.le_refl 8)) as M80.
pose proof (field_of_region_any _ _ 9%nat mf _ _ _ _ _ 176 8%N (SLit 0x7fff8000) HRmf U9h ltac:(sb_in) (Z.le_refl 8)) as M176.
cbn [sv_denot] in M184, M48, M80, M176. rewrite E16h in M184, M48, M80.
change (N.to_nat 8) with 8%nat in M184, M48, M80, M176. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in M184, M48, M80, M176.
rewrite (unsigned_lit_small SF) in M184, M48, M80 by (clear - HSF0 HSF1 C1; lia).
rewrite unsigned_lit_small in M184, M48, M80 by (clear - HSF0 HSF1 C1; lia).
rewrite unsigned_lit_small in M176 by (clear - HSF0; lia).
rewrite Z.mod_small in M184, M48, M80, M176 by (clear - HSF0 HSF1 C1; lia).
rewrite Z.add_0_r in M80.
destruct HRsh as (_ & _ & _ & Hcs2). cbn [YP09.r_chunks YP09.r_base base_val] in Hcs2. rewrite U19h in Hcs2.
assert (T44 : aview SEGS (w_H W3) (ms_mem msE) (SHADOW_OFF + SF / 8 + 44) = Some 0)
  by (rewrite <- Esh; apply (sb_cell_of _ _ _ sh _ 44 0 Hcs2); [sb_in | clear - HSF0; lia]).
assert (T45 : aview SEGS (w_H W3) (ms_mem msE) (SHADOW_OFF + SF / 8 + 45) = Some 0)
  by (rewrite <- Esh; apply (sb_cell_of _ _ _ sh _ 45 0 Hcs2); [sb_in | clear - HSF0; lia]).
assert (T46 : aview SEGS (w_H W3) (ms_mem msE) (SHADOW_OFF + SF / 8 + 46) = Some 0)
  by (rewrite <- Esh; apply (sb_cell_of _ _ _ sh _ 46 0 Hcs2); [sb_in | clear - HSF0; lia]).
assert (T47 : aview SEGS (w_H W3) (ms_mem msE) (SHADOW_OFF + SF / 8 + 47) = Some 0)
  by (rewrite <- Esh; apply (sb_cell_of _ _ _ sh _ 47 0 Hcs2); [sb_in | clear - HSF0; lia]).
assert (T48 : aview SEGS (w_H W3) (ms_mem msE) (SHADOW_OFF + SF / 8 + 48) = Some 6)
  by (rewrite <- Esh; apply (sb_cell_of _ _ _ sh _ 48 6 Hcs2); [sb_in | clear - HSF0; lia]).
assert (T54 : aview SEGS (w_H W3) (ms_mem msE) (SHADOW_OFF + SF / 8 + 54) = Some 0)
  by (rewrite <- Esh; apply (sb_cell_of _ _ _ sh _ 54 0 Hcs2); [sb_in | clear - HSF0; lia]).
assert (T55 : aview SEGS (w_H W3) (ms_mem msE) (SHADOW_OFF + SF / 8 + 55) = Some 4)
  by (rewrite <- Esh; apply (sb_cell_of _ _ _ sh _ 55 4 Hcs2); [sb_in | clear - HSF0; lia]).
destruct (sb_id_shadow (aview SEGS (w_H W3) (ms_mem msE)) SF HSF64 T44 T45 T46 T47 T48) as [BSE ZSE].
(* what the whole segment kept: the two runs before the call, the call, the runs after it *)
assert (NWS : forall a, mf <= a < sp0 -> ~ (mf + 48 <= a < mf + 192) -> ~ sb_win mf sh a).
{ intros a Ha Hn [H | [H | H]]; [clear - Ha H; lia | exact (Hn H) | clear - Ha H Hsh1 Hmf0; lia]. }
assert (NWF : forall a, SF <= a < SF + 1024 -> ~ sb_win mf sh a).
{ intros a Ha [H | [H | H]]; [clear - Ha H HSF1 Hmf0; lia | clear - Ha H HSF1 Hmf0; lia |].
  apply (fshadow_not_app SF 128 SF 1024 a); [exact HSF0 | clear - HSF1 C1; lia | exact HSFapp | | exact Ha].
  rewrite Esh in H. unfold SHADOW_OFF in H. clear - H. lia. }
assert (TOT : forall a, 0 <= a < 2 ^ 64 -> ~ sb_win mf sh a ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) (ms_mem ms0) a ->
  aview SEGS (w_H W3) (ms_mem msE) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hz Hi. rewrite (KP a Ha Hz), Hi. exact (KP1 a Ha Hz). }
assert (STACKK : forall a, mf <= a < sp0 -> ~ (mf + 48 <= a < mf + 192) ->
  aview SEGS (w_H W3) (ms_mem msE) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hn. apply TOT; [clear - Ha Hmf0 Hmfb Hshi H47 C1; lia | exact (NWS a Ha Hn) |].
  apply KK1; [clear - Ha Hmf0 Hmfb Hshi H47 C1; lia | clear - Ha; lia |].
  cbv beta. unfold V_id, reac_identity_init.IDENT_SIZE. clear - Ha HSF1 Hmf0. lia. }
assert (FRAMEK : forall a, SF <= a < SF + 1024 -> ~ (SF + V_id <= a < SF + V_id + 38) ->
  aview SEGS (w_H W3) (ms_mem msE) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hn. apply TOT; [clear - Ha HSF0 HSF1 C1; lia | exact (NWF a Ha) |].
  apply (KK4 4 pos a Hin4); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFa, HFB; clear - Ha; lia |].
  cbv beta. unfold reac_identity_init.IDENT_SIZE. exact Hn. }
assert (VMS : forall a (n : nat) v, mf <= a -> a + Z.of_nat n <= sp0 -> (a + Z.of_nat n <= mf + 48 \/ mf + 192 <= a) ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W3 (ms_mem msE)) a n v).
{ intros a n v H1 H2 H3 Hv. apply (val_mem_moved SEGS (w_H W2) (w_H W3) mem2 (ms_mem msE) a a n v); [|exact Hv].
  intros kk Hkk. apply STACKK; clear - H1 H2 H3 Hkk; lia. }
assert (HID : forall j, 0 <= j < 38 -> aview SEGS (w_H W3) (ms_mem msE) (SF + V_id + j) = Some 0).
{ intros j Hj. rewrite (KP (SF + V_id + j) ltac:(unfold V_id; clear - Hj HSF0 HSF1 C1; lia)
    (NWF (SF + V_id + j) ltac:(unfold V_id; clear - Hj; lia))).
  exact (Hzero3 j ltac:(unfold reac_identity_init.IDENT_SIZE; exact Hj)). }
assert (HINB : bytes_at8 W3 (ms_mem msE) (e_p g) (e_pl g)).
{ unfold bytes_at8 in *. apply (sb_garr8_moved (w_H W2) (w_H W3) mem2 (ms_mem msE) _ _); [|exact Hinb].
  intros j Hj. rewrite length_map in Hj. rewrite <- Hlen in Hj.
  destruct Hinp as [[Hn0 _] | [[Hn0 Hn26] Hine]]; [clear - Hj Hn0; lia|].
  assert (Hine2 : In (e_p g, e_n g) (ablocks B ly2 S2)).
  { destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). exact Hine. }
  destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 (e_p g) (e_n g) HAR2 Hine2) as (_ & Hp4096 & Hpce & Hpapp & _).
  pose proof (req_size_pos (e_n g) ltac:(lia)) as Hrq.
  pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 (e_p g) (e_n g) 4 pos HAR2 Hine2 Hin4) as Hdf.
  unfold zdisjoint in Hdf. cbn [fst snd] in Hdf. rewrite EFa, HFB in Hdf.
  apply TOT; [clear - Hj Hpce Hp4096 Hrq C1; lia | |].
  - intros [H | [H | H]]; [clear - H Hj Hpce Hrq Hmf0; lia | clear - H Hj Hpce Hrq Hmf0; lia |].
    apply (fshadow_not_app SF 128 (e_p g) (req_size (e_n g)) (e_p g + j));
    [exact HSF0 | clear - HSF1 C1; lia | exact Hpapp | | clear - Hj Hrq; lia].
    rewrite Esh in H. unfold SHADOW_OFF in H. clear - H. lia.
  - apply (KK2 (e_p g) (e_n g) j Hine2); [clear - Hj Hrq; lia |].
    cbv beta. unfold V_id, reac_identity_init.IDENT_SIZE. clear - Hdf Hj Hrq. lia. }
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as [Efd Efs].
apply SRr_ret.
unfold inv_B_end, acut. pmkst HS.
exists ly3, S3, (ms_regs msE), (ms_mem msE). eexists.
split; [reflexivity|].
split; [exact HJ3|].
split; [rewrite Hfr3; exact Hfrs|].
split; [unfold EV_LLVMF; clear - HSF0; lia|].
split; [rewrite Z.mul_0_l; apply HMT0|].
split; [apply (mo_ok_step MT MTL S2 S3 0 _); [rewrite Z.add_0_l; exact MOK | apply HMT0]|].
split.
{ unfold ecommon. change (e_sp0 g) with sp0. change (SFa g pos) with SF.
  split; [exact F2|]. split; [exact F9|]. split; [exact F8|].
  split; [exact Hmfb|]. split; [exact Hmf32|]. split; [exact F3|]. split; [exact F4|].
  split; [exact F19|].
  split; [exact M80|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | right; clear - Hmfb; lia | exact V192]|].
  split; [exact M176|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | right; clear - Hmfb; lia | exact Vra]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | right; clear - Hmfb; lia | exact Vs0]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | right; clear - Hmfb; lia | exact V24]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | right; clear - Hmfb; lia | exact V32]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | right; clear - Hmfb; lia | exact V40]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | right; clear - Hmfb; lia | exact V48]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | right; clear - Hmfb; lia | exact V56]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | right; clear - Hmfb; lia | exact V64]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | right; clear - Hmfb; lia | exact V72]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | right; clear - Hmfb; lia | exact V80b]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | right; clear - Hmfb; lia | exact V88]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | right; clear - Hmfb; lia | exact V96]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | right; clear - Hmfb; lia | exact V104]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | left; clear - Hmfb; lia | exact Vmf24]|].
  split.
  { apply (val_mem_moved SEGS (w_H W2) (w_H W3) mem2 (ms_mem msE) (SF + 1016) (SF + 1016) 8 _); [|exact Vflag].
    intros kk Hkk. apply FRAMEK; unfold V_id; clear - Hkk; lia. }
  split; [exact HPRE|].
  split; [intros fd; rewrite Efd; reflexivity|].
  split; [exact Efs|].
  exact HINB. }
unfold id_at, hblocks, bytes_at8, sh_zero, sh_blk. change (SFa g pos) with SF.
split.
{ split; [|split].
  - unfold m_id. cbn [SlotModel.rec_id]. unfold RcIdentModel.ID0. rewrite map_repeat.
    change (bv_unsigned (RcIdentModel.zb 0)) with 0. intros j Hj. rewrite repeat_length in Hj.
    rewrite nth_repeat. split; [|clear - Hj; lia]. apply sb_val_mem1.
    exact (HID (Z.of_nat j) ltac:(unfold RcIdentModel.ID_SIZE in Hj; clear - Hj; lia)).
  - unfold V_id, N_id. exact ZSE.
  - unfold V_id, N_id. exact BSE. }
split; [split; [eapply Permutation_trans; [exact Hperm3 | exact (proj1 Hbl)] | constructor]|].
split; [unfold V_id; exact M184|].
split; [unfold V_hw; exact M48|].
split; [exact F10'|]. split; [exact F11|]. split; [exact F12|]. split; [exact F18|]. split; [exact F26|].
split.
- replace (shadow_addr (SF + V_hw)) with (SHADOW_OFF + SF / 8 + 54) by (unfold shadow_addr, V_hw; clear - HSF64; lia).
  exact T54.
- replace (shadow_addr (SF + V_hw + 8)) with (SHADOW_OFF + SF / 8 + 55) by (unfold shadow_addr, V_hw; clear - HSF64; lia).
  exact T55.
Qed.

End c.
End b.
End a.
