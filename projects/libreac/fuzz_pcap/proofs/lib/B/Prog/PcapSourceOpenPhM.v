From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the MIDDLE of pcap_source_open's walk on libreac v1.9.0's ASan+UBSan build
   (fuzz_pcap.asan-ubsan 0x811e0, listing offset AF_pcap_source_open = 0xa58, 246 instructions): from the return of
   libreac_fuzz_fopen (0x812f8, lib/B/Prog/PcapSourceOpenPhF.v's cut op_fopen_ret) to the two cuts of
   lib/B/Prog/PcapSourceOpenPh.v, 0x813f8 (op_gi_null) and 0x8138c (op_gi_read). op_from_fopen proves PhF's
   op_from_fopen_stmt from Ph's two `op_from`s (lib/B/Prog/PcapSourceOpenB.v proves those); lib/B/Prog/PcapSourceOpen.v
   composes. At ossv/recipes 25e3d17bdb50 (2026-10-29), this image had no released proof (rule 24; a Theorem Labs lane, 22:35Z); the released v1.8 UBSan proof
   lib/U/Prog/pcap_source_open.v is the guard template only.

   THE STRETCH, at this image's pcs:
   - 0x812f8 `beqz s3` (G5a) to the `unimp` at 0x8153c; 0x812fc a3 := a0 (f); 0x81300 `andi a0,s3,7` / 0x81304
     `bnez a0` (G5b) to 0x8153c;
   - 0x81308 / 0x8130c s8 := (ps >> 3) + s7; 0x81310 `lbu` / 0x81314 `bnez` (to report_store8, 0x81598); 0x81318
     ps->f := f;
   - ps + 12 (0x8131c..0x8132c, slow block 0x81540), ps + 16 (0x81334..0x81344, 0x81550), ps + 20 (0x8134c..0x8135c,
     0x81560): each shadow test, then the zero store (0x81330 `sw`, 0x81348 `sw`, 0x81360 `sh`);
   - 0x81364 `beqz a3`: f = NULL goes to 0x813f8, the null cut (pm_null_cut builds op_gi_null);
   - else 0x81368 s4 := F + 32, 0x8136c..0x81374 the header buffer's three shadow bytes := 0 (OSH_in), a1 = 1,
     a2 = s9 = 24, a0 = s4, and 0x81388 `jal` the fread wrapper's trampoline 0x415d0, bound through AFREAD
     (lib/A/Stdio/PFreadISpec.v afread_spec, the caller-journal form; pm_fread_pre builds its afread_pre: the
     destination F + 32 in this call's own frame with its shadow in scope, the FILE block's write right from
     op_fopen_ret's footprint fact, the data buffer off the callee's window); its return address 0x8138c is the read
     cut (pm_read_cut builds op_gi_read from fread's post).
   The token run walks 0x812f8..0x81364 and the `jal`; 0x81368..0x81384 store into the shadow band, which the token
   engine refuses while a window lies there uncovered (cells_safe_b, Reusable/YCbn.v:115-119), so that stretch is
   walked by the plain run, as PcapSourceOpen.v walks 0x8124c..0x812f0.

   THE GUARDS, both decided NOT taken by the token run from the facts pm_entry proves of atom 19 (s3 = ps): HPTR 3,
   i.e. 4096 <= ps (ps lies in a frame of the caller, frames_bounds; the statement's ps <> 0) and ps mod 2^3 = 0 (the
   statement's ps mod 8 = 0). The deciding steps are those of lib/B/Prog/PcapSourceClose.v:18-27.
     0x812f8 (G5a `beqz s3`): refuted by decide_cond2 (Reusable/YP0e.v:932) through decide_eq (Reusable/YP0m.v:658-672),
              whose SOff / SLit arm (:665-666) finds ps's range [4096, ...] disjoint from 0. Template:
              lib/U/Prog/pcap_source_open.v:114 (open_null) and :334 (open_mid) at c8557374ad2e, premise
              bv_unsigned s0 <> 0 at :93 / :290.
     0x81304 (G5b `andi a0,s3,7` / `bnez a0`): s_and_ptr (Reusable/YP0m.v:969-980) rewrites ps & 7 to 0 from the
              alignment fact, so the BC_NE test is refuted as G5a's. Template :115 / :335, premise bv_unsigned s0 mod 8
              = 0 at :93 / :290.
   The earlier walk of this image, pcap_source_open_fo.v (sha256 b7425f5b4c84; internal record) on a working branch
   a8ccd33b1a7, decides the same branches at :66 / :68 (pso_fo_null) and :132 / :134 (pso_fo_hit).

   THE REPORT EDGES (FORM A). Every shadow test of the stretch reads through ps's shadow entry pm_SH = [mkSHE 19 0 24]
   (pm_shent_ok, from op_fopen_ret's range_addressable of ps's 24 bytes; ps is 8-aligned, so each shadow byte read is
   0): tok_load (Reusable/YCbn.v:173-195) reads the byte as a token and tok_branch (:236-288) decides each `bnez` NOT
   taken (sound by tok_branch_sound :1179-1341, through need_sound :780-794 and cellval_zero_iff :1004-1023).
     0x81314 (to the report_store8 block 0x81598): refuted by tok_branch on ps's shadow byte (0x81310);
     0x8132c (to the slow block 0x81540): on ps + 12's (0x81328);
     0x81344 (to 0x81550): on ps + 16's (0x81340);
     0x8135c (to 0x81560): on ps + 20's (0x81358);
   each from op_fopen_ret's range_addressable rd SHADOW_OFF ps 24. No slow block and no report call is reached.
   Templates: pcap_source_open_fo.v (sha256 b7425f5b4c84; internal record) :71, :76, :80, :84 (pso_fo_null) and :137, :142, :146, :150 (pso_fo_hit).

   The section hypotheses are named as the other walk files name them: LAWS (AR_laws), ASIL (asource_img_laws), and
   AFREAD (the fread wrapper's contract at the trampoline). getr / mkst / seg_rom come from YK11; nothing from lib/Lib
   is imported. Every number is read from the pin fuzz_pcap.asan-ubsan (sha256 9e66f771f22af67a...). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0s YI16 YG0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 PcapImgEnd YE00 YG0p YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSyms PcapList PcapAddr PcapPa PcapPaLib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import YC1g YC1h YC85 PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFmemopenISpec PFreadM PFreadISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapFuzzFopenDefs PcapSourceOpenDefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceOpenPh PcapSourceOpenPhF.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the pcs of the stretch, as listing offsets (address - 0x80788) ---- *)
Definition OP_SH_IN : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_open + 0x18c) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.       (* 0x8136c `sb zero,4(s5)`: the first of the buffer's three shadow stores *)
Definition OP_FREAD_CALL : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_open + 0x1a8) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.  (* 0x81388 `jal` the fread wrapper's trampoline 0x415d0 *)
Lemma OP_MID_pin : pcap_text + OP_SH_IN = (symaddr (Symbols.AsanUbsan.s_pcap_source_open + 0x18c)%Z) /\ pcap_text + OP_FREAD_CALL = (symaddr (Symbols.AsanUbsan.s_pcap_source_open + 0x1a8)%Z).
Proof. split; reflexivity. Qed.

(* ---- the symbolic state at the fopen return ---- *)
Definition pm_SB : Z := 0x7fff8000.
Definition pm_Bx : sv := SOff 32 0.
Definition pm_span : Z * Z := (pm_SB, pm_SB + 2 ^ 44 - 1).
Definition pm_extra : list word := [w64 pm_SB].
Definition r_pmA : YP09.region := YP09.mkRegion (Some 19%nat) 0 8 0 8 [].
Definition r_pmB : YP09.region := YP09.mkRegion (Some 19%nat) 12 22 12 22 [].
Definition r_pmSH : YP09.region := YP09.mkRegion (Some 21%nat) 0 16 4 7 [].
Definition pm_sr : list sv := sr_set sr_atoms 23%bv (SOff 32 0).
Definition pm_facts : facts := mkFacts [(19%nat, HPTR 3); (32%nat, mkAF pm_SB pm_SB 0)] [] [].
Definition ss_pm (pc : Z) : sstate := mkSS pc pm_sr [r_pmA; r_pmB] None pm_facts.
Definition pm_SH : list shent := [mkSHE 19 0 24].
Definition pm_keepN : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 25; 26; 27]%bv.
Definition pm_keepR : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 21; 22; 26; 27]%bv.

(* A register's symbolic value, not normalized (PcapSourceOpen.v:96-106). *)
Ltac pm_prreg_raw HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
Ltac pm_norm_pi HS := lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let v := eval vm_compute in ss in change ss with v in HS end.
(* A region's window closed (PcapSourceOpen.v:157-164): the token engine's cells_safe_b (YCbn.v:115-119) refuses a
   window in the shadow band that no shadow entry covers. *)
Ltac pm_set_ro HS i :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
    let r := eval vm_compute in (nth i (ss_mem ssx) r_pmA) in
    let HS3 := fresh "HS3" in
    pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl
      ltac:(vm_compute; reflexivity)
      (region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
        ltac:(intros o Ho; lia))) as HS3;
    clear HS; rename HS3 into HS; pm_norm_pi HS end.
(* The write rights of a run: ps's two windows (a frame of the caller's own) and the three shadow bytes of this
   call's frame F. *)
Ltac pm_awr cid pos fpos Hown EFA U19 U21 F :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply awr_ok_cons_gen; [reflexivity | exact U19 | cbn [YP09.r_wlo YP09.r_whi]; intros ?a ?Ha;
      right; right; right; exists cid, pos; split; [right; exact Hown|]; left; unfold in_zr; cbn [fst snd];
      rewrite EFA; lia |]
  | eapply awr_ok_cons_gen; [reflexivity | exact U21 | cbn [YP09.r_wlo YP09.r_whi]; intros ?a ?Ha;
      right; right; right; exists 1, fpos; split; [left; reflexivity|]; right; unfold in_zr, shadow_addr;
      cbn [fst snd]; rewrite EFA; change (fs_frame_bytes 1 / 8) with 16; fold F; lia |] ].
(* The names op_fopen_ret's conjuncts get, in PcapSourceOpenPhF.v's order. *)
Ltac pm_unpack_fr HFR :=
  destruct HFR as (Hpc & Hrv & Hsvc & Hrom & Hfr & Hfcsr & HJ & Hfrs2 & Hnin2 & Hnev2 & HfsS2 & R2 & R9 & R8 & R18 &
    R22 & R19 & R20 & R21 & R23 & R10 & R3 & R4 & R25 & R26 & R27 & Hra & Hsav & HMG & HO8 & HO16 & HFLP & Hsh &
    Hslot & HFpres & HPS0 & HRA & HKEPT & HROD & HMETA & Hfds & Hfs & Hch & Hn0 & Hn1).
(* A callee-saved register across a call: aregs_preserved, then its value at the call (the keep list). *)
Ltac pm_regq HP QK r rb R :=
  etransitivity; [exact (HP r ltac:(unfold acallee_saved; lia))|];
  etransitivity; [exact (QK rb ltac:(cbn; tauto))|]; exact R.

(* ---- arithmetic -------------------------------------------------------------------------------------------- *)
Lemma pm_w64_unsigned : forall x : word, w64 (bv_unsigned x) = x.
Proof. intros x. unfold w64. apply Z_to_bv_bv_unsigned. Qed.

Lemma pm_wvb_fds_fs : forall l X m, m_fds (with_vm_backing l X m) = m_fds m /\ m_fs (with_vm_backing l X m) = m_fs m.
Proof. intros l X [fd [maps lazy mat] io fs proc lim tm]. split; reflexivity. Qed.

Lemma pm_div8 : forall a, a mod 64 = 0 -> a / 8 = 8 * (a / 64) /\ a = 64 * (a / 64).
Proof.
intros a H. pose proof (Z_div_mod_eq_full a 64) as E. rewrite H, Z.add_0_r in E. split; [|exact E].
symmetry. apply (Z.div_unique a 8 (8 * (a / 64)) 0); [left; lia | lia].
Qed.

Lemma pm_div8_add : forall m c, (8 * m + c) / 8 = m + c / 8.
Proof. intros m c. rewrite Z.mul_comm, Z.div_add_l by lia. reflexivity. Qed.

(* The header buffer F + 32 .. F + 56 lies in F's shadow bytes 4 .. 6. *)
Lemma pm_hdr_shadow : forall F x, F mod 64 = 0 -> F + 32 <= x < F + 56 ->
  x / 8 = F / 8 + (4 + (x - F - 32) / 8) /\ 4 <= 4 + (x - F - 32) / 8 < 7.
Proof.
intros F x HF Hx. destruct (pm_div8 F HF) as [E8 E64].
assert (Ej : 0 <= (x - F - 32) / 8 < 3) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
split; [|lia].
replace x with (8 * (F / 8 + 4) + (x - F - 32)) at 1 by lia.
rewrite pm_div8_add. lia.
Qed.

(* The shadow hull of the header buffer is F's first shadow granule. *)
Lemma pm_hull_bounds : forall F, F mod 64 = 0 ->
  (SHADOW_OFF + (F + 32) / 8) / 8 * 8 = SHADOW_OFF + F / 8 /\
  (SHADOW_OFF + (F + 32 + 24 - 1) / 8) / 8 * 8 + 8 = SHADOW_OFF + F / 8 + 8.
Proof.
intros F HF. destruct (pm_div8 F HF) as [E8 E64].
assert (A1 : (F + 32) / 8 = 8 * (F / 64) + 4).
{ replace (F + 32) with (8 * (8 * (F / 64) + 4) + 0) by lia. rewrite pm_div8_add. change (0 / 8) with 0. lia. }
assert (A2 : (F + 32 + 24 - 1) / 8 = 8 * (F / 64) + 6).
{ replace (F + 32 + 24 - 1) with (8 * (8 * (F / 64) + 6) + 7) by lia. rewrite pm_div8_add. change (7 / 8) with 0. lia. }
unfold SHADOW_OFF. rewrite A1, A2, E8.
replace (2147450880 + (8 * (F / 64) + 4)) with (8 * (268431360 + F / 64) + 4) by lia.
replace (2147450880 + (8 * (F / 64) + 6)) with (8 * (268431360 + F / 64) + 6) by lia.
rewrite !pm_div8_add. change (4 / 8) with 0. change (6 / 8) with 0. lia.
Qed.

(* A byte outside F's 128 bytes has its shadow outside F's 16 shadow bytes. *)
Lemma pm_sh_apart : forall F x, F mod 64 = 0 -> 0 <= x -> (x < F \/ F + 128 <= x) ->
  x / 8 < F / 8 \/ F / 8 + 16 <= x / 8.
Proof.
intros F x HF Hx Hr. destruct (pm_div8 F HF) as [E8 E64].
destruct Hr as [Hr|Hr]; [left | right].
- apply Z.div_lt_upper_bound; lia.
- apply Z.div_le_lower_bound; lia.
Qed.

(* osp1 is 32-aligned, at most 127 below the entry sp (lib/B/Prog/PcapSourceOpenB.v:1072-1077). *)
Lemma pm_osp1_facts : forall x, 0 <= x -> x mod 16 = 0 ->
  x - 127 <= 32 * ((x - 96) / 32) <= x - 96 /\ (32 * ((x - 96) / 32)) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod (x - 96) 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (x - 96) 32 ltac:(lia)) as M.
split; [lia|]. replace (32 * ((x - 96) / 32)) with ((2 * ((x - 96) / 32)) * 16) by lia. apply Z.mod_mul. lia.
Qed.

Lemma pm_rdword_agree : forall (rd rd' : Z -> option Z) a,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. unfold rdword.
assert (H0 : rd' a = rd a) by (pose proof (H 0 ltac:(lia)) as X; rewrite Z.add_0_r in X; exact X).
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

Lemma pm_denot_off : forall E n v c, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n c) = w64 (v + c).
Proof. intros E n v c Hn Hv. cbn [sv_denot]. rewrite Hn. unfold w64. rewrite unsigned_lit_small by exact Hv. reflexivity. Qed.

Lemma pm_ra_frame : forall (rd rd' : Z -> option Z) a n,
  range_addressable rd SHADOW_OFF a n ->
  (forall x, a <= x < a + n -> rd' (shadow_of_addr SHADOW_OFF x) = rd (shadow_of_addr SHADOW_OFF x)) ->
  range_addressable rd' SHADOW_OFF a n.
Proof. intros rd rd' a n HR Hk x Hx. destruct (HR x Hx) as (s & Hs & Ho). exists s. rewrite Hk by exact Hx. split; [exact Hs | exact Ho]. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Section d.
Context {PI : PAImg pcap_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Abbreviation VAL := (@pa_val _ pcap_listing PI).
#[local] Abbreviation SIGMA := (@pa_sigma _ pcap_listing PI).
#[local] Abbreviation BASE := (@pa_val _ pcap_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* A symbolic state over a machine state given by its fields (lib/B/Prog/PcapSourceOpenB.v:173-185). *)
Lemma pm_mid_st_ok : forall E pc sr (rs : smem) (G : facts) H (ms : machine_state),
  ms_fregs ms = fp_regs -> ms_pc_val ms = Z_to_bv 64 (BASE + pc) -> ms_svc_pending ms = None -> ms_resv ms = None ->
  ms_fcsr ms = fp_csr -> ms_rom ms = seg_rom SEGS ->
  regs_ok E sr (ms_regs ms) -> regions_wf rs = true -> Forall (region_ok SEGS E (mrestrict H (ms_mem ms))) rs ->
  pairwise_disjoint E rs -> facts_ok E G ->
  st_ok_pi SEGS VAL E (mkSS pc sr rs None G) (restrict H ms).
Proof.
intros E pc sr rs G H ms H1 H2 H3 H4 H5 H6 Hsr Hwf Hrs Hpd HG.
unfold st_ok_pi, abs_ss, setpc, st_ok. cbn [restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem
  ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|].
split; [exact Hsr|]. split; [| exact HG]. split; [exact Hwf|]. split; [exact Hrs | exact Hpd].
Qed.

Lemma pm_ly_F : forall B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
  (forall c q, frame_addr ly' c q = frame_addr ly c q) /\ (forall c q, flag_addr ly' c q = flag_addr ly c q).
Proof.
intros B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k (_ & Hly & _).
destruct Hly as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr, flag_addr. rewrite EF. split; reflexivity.
Qed.

(* ---- what a byte-wise memory equality carries (lib/B/Prog/PcapSourceOpenB.v:196-283) ---- *)
Lemma pm_vm_frame : forall (m m' : word -> option byte) a n v,
  (forall x, a <= x < a + Z.of_nat n -> mbyte SEGS m' x = mbyte SEGS m x) ->
  val_mem SEGS m a n v -> val_mem SEGS m' a n v.
Proof. intros m m' a n v Hfr Hv k Hk. rewrite Hfr by lia. exact (Hv k Hk). Qed.

Ltac pm_vmf Hfr H := eapply pm_vm_frame; [| exact H]; intros ?x ?Hx; apply Hfr.

Lemma pm_asource_none_frame : forall K (m m' : word -> option byte),
  (forall a, asrc_env_addr K a -> mbyte SEGS m' a = mbyte SEGS m a) ->
  asource_none SEGS K m -> asource_none SEGS K m'.
Proof.
intros K m m' Hfr ((Hth & Hnl & Hlk & Hmode & Hms & (cv & Hcv & Hc)) & Hhead).
unfold asource_none, asrc_stdio_env, as_ofl_head in *.
split; [split; [|split; [|split; [|split; [|split]]]]|].
- pm_vmf Hfr Hth. unfold asrc_env_addr. cbn in Hx. lia.
- pm_vmf Hfr Hnl. unfold asrc_env_addr. cbn in Hx. lia.
- pm_vmf Hfr Hlk. unfold asrc_env_addr. cbn in Hx. lia.
- apply (garr8_frame SEGS m m' _ _ Hmode). intros x Hx. apply Hfr. unfold asrc_env_addr.
  cbn [length src_mode_Z app] in Hx. cbn in Hx. lia.
- apply (garr8_frame SEGS m m' _ _ Hms). intros x Hx. apply Hfr. unfold asrc_env_addr.
  cbn [length src_modeset_Z app] in Hx. cbn in Hx. lia.
- exists cv. split; [exact Hcv|]. pm_vmf Hfr Hc. unfold asrc_env_addr. cbn in Hx. lia.
- pm_vmf Hfr Hhead. unfold asrc_env_addr. cbn in Hx. lia.
Qed.

Lemma pm_asource_at_frame : forall K (m m' : word -> option byte) f b C p,
  (forall a, (f <= a < f + SRC_FILE_BLOCK) \/ (b <= a < b + Z.of_nat (length C)) \/ asrc_env_addr K a ->
     mbyte SEGS m' a = mbyte SEGS m a) ->
  asource_at SEGS K m f b C p -> asource_at SEGS K m' f b C p.
Proof.
intros K m m' f b C p Hfr (Wn & cpos & fl & md & H). cbv zeta in H.
destruct H as (Hp0 & Hp1 & Hp2 & Hn63 & Hwrap & Hcp & HW & Hbok & Hgb & Hst & Hwin & Hfl & Hfl24 & Hmd & Hcpos & Henv & Hhead & Hf0).
assert (HF : forall x, f <= x < f + SRC_FILE_BLOCK -> mbyte SEGS m' x = mbyte SEGS m x) by (intros x Hx; apply Hfr; left; exact Hx).
assert (HE : forall x, asrc_env_addr K x -> mbyte SEGS m' x = mbyte SEGS m x) by (intros x Hx; apply Hfr; right; right; exact Hx).
destruct Hst as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S168 &
  S18 & S19 & S20 & Sf & Sal & Sb & Sdisj).
exists Wn, cpos, fl, md. cbv zeta.
split; [exact Hp0|]. split; [exact Hp1|]. split; [exact Hp2|]. split; [exact Hn63|]. split; [exact Hwrap|].
split; [exact Hcp|]. split; [exact HW|].
split; [exact Hbok|].
split; [apply (garr8_frame SEGS m m' _ _ Hgb); intros x Hx; apply Hfr; right; left; exact Hx|].
split.
{ unfold source_static, SRC_COOKIE_OFF, SRC_BUF_OFF, SRC_BUFSIZ, SRC_MODE_R, U32M1 in *.
  split; [pm_vmf HF S1; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [pm_vmf HF S2; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [pm_vmf HF S3; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [pm_vmf HF S4; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [pm_vmf HF S5; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [pm_vmf HF S6; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [pm_vmf HF S7; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [pm_vmf HF S8; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [pm_vmf HF S9; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [pm_vmf HF S10; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [pm_vmf HF S11; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [pm_vmf HF S12; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [pm_vmf HF S13; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [pm_vmf HF S14; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [pm_vmf HF S15; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [pm_vmf HF S16; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [pm_vmf HF S17; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [pm_vmf HF S168; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [pm_vmf HF S18; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [pm_vmf HF S19; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [pm_vmf HF S20; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [exact Sf|]. split; [exact Sal|]. split; [exact Sb | exact Sdisj]. }
split.
{ unfold source_window, SRC_BUF_OFF, SRC_BUFSIZ in *. destruct Hwin as [(-> & W1 & W2) | (i & Hi0 & Hi1 & W1 & W2 & W3)].
  - left. split; [reflexivity|]. split; [pm_vmf HF W1 | pm_vmf HF W2]; unfold SRC_FILE_BLOCK; cbn in Hx; lia.
  - right. exists i. split; [exact Hi0|]. split; [exact Hi1|].
    split; [pm_vmf HF W1; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
    split; [pm_vmf HF W2; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
    apply (garr8_frame SEGS m m' _ _ W3). intros x Hx. apply HF. unfold SRC_FILE_BLOCK. lia. }
split.
{ unfold source_flags in *. destruct Hfl as [Hfl1 Hfl2]. split; [|exact Hfl2]. pm_vmf HF Hfl1. unfold SRC_FILE_BLOCK. cbn in Hx. lia. }
split; [exact Hfl24|].
split.
{ unfold source_mode in *. destruct Hmd as [Hmd1 Hmd2]. split; [|exact Hmd2]. pm_vmf HF Hmd1. unfold SRC_FILE_BLOCK. cbn in Hx. lia. }
split; [pm_vmf HF Hcpos; unfold SRC_COOKIE_OFF, SRC_FILE_BLOCK in *; cbn in Hx; lia|].
split.
{ unfold asrc_stdio_env in *. destruct Henv as (Hth & Hnl & Hlk & Hmode & Hms & (cv & Hcv & Hc)).
  split; [pm_vmf HE Hth; unfold asrc_env_addr; cbn in Hx; lia|].
  split; [pm_vmf HE Hnl; unfold asrc_env_addr; cbn in Hx; lia|].
  split; [pm_vmf HE Hlk; unfold asrc_env_addr; cbn in Hx; lia|].
  split; [apply (garr8_frame SEGS m m' _ _ Hmode); intros x Hx; apply HE; unfold asrc_env_addr; cbn in Hx; lia|].
  split; [apply (garr8_frame SEGS m m' _ _ Hms); intros x Hx; apply HE; unfold asrc_env_addr; cbn in Hx; lia|].
  exists cv. split; [exact Hcv|]. pm_vmf HE Hc. unfold asrc_env_addr. cbn in Hx. lia. }
split; [pm_vmf HE Hhead; unfold asrc_env_addr, as_ofl_head in *; cbn in Hx; lia | exact Hf0].
Qed.

(* A one-byte zero read back through the view. *)
Lemma pm_aview0 : forall H (m : word -> option byte) a, val_mem SEGS (mrestrict H m) a 1 0 -> aview SEGS H m a = Some 0.
Proof.
intros H m a V. unfold aview. pose proof (V 0%nat ltac:(lia)) as X. rewrite Z.add_0_r in X. rewrite X.
vm_compute. reflexivity.
Qed.

Section e.
Variable B : asyms.
Variable K : asource_syms.
Variable MT : ameter_ops.
Variable FM_RA : Z.
Variable CTX : list (list Z).
Variable roimg : (word -> option byte) -> Prop.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ASIL : asource_img_laws SK SEGS B K.
(* The fread wrapper's contract (lib/A/Stdio/PFreadISpec.v afread_spec, the caller-journal form) at this image's
   trampoline 0x415d0. *)
Hypothesis AFREAD : afread_spec SK SEGS B K (SIGMA PS___interceptor_trampoline_fread).

(* The stream's environment lies in the image (asil_env). *)
Lemma pm_src_env_img : forall a, asrc_env_addr K a -> 0x10000 <= a < pcap_img_end.
Proof. intros a Ha. exact (pa_img_range a (proj1 (asil_env _ _ _ _ ASIL a Ha))). Qed.

(* The bytes of this call's frame F and of its 16 shadow bytes are none of the caller's (PcapSourceOpenB.v:587-660,
   without the flag). *)
Lemma pm_apart : forall (cx : ocx) fpos ly3 S3 W3 mem3 md3 kk a,
  op_pre SK B K MT FM_RA CTX roimg cx ->
  ajournal SEGS B (o_STK cx) (o_sp0 cx) (o_FP cx) (o_ly cx) (o_S cx) (o_W0 cx) (o_mem0 cx) (o_md0 cx)
    ((OP_CID, fpos) :: o_own cx) ly3 S3 W3 mem3 md3 kk ->
  (oF cx fpos <= a < oF cx fpos + 128) \/ (oSH cx fpos <= a < oSH cx fpos + 16) ->
  4096 <= a < alloc_ceiling /\ ~ in_img SEGS a /\
  (forall b m, In (b, m) (ablocks B ly3 S3) -> ~ (b <= a < b + req_size m)) /\
  (forall c q, In (c, q) (frames (o_Sc cx)) ->
     ~ in_zr a (frame_rng (o_lyc cx) (c, q)) /\ ~ in_zr a (shadow_addr (frame_addr (o_lyc cx) c q), fs_frame_bytes c / 8)).
Proof.
intros cx fpos ly3 S3 W3 mem3 md3 kk a HPRE HJ Ha.
destruct cx as [STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k regs ch ps n b M C cid pos].
unfold oSH, oF, op_pre in *. cbn [o_STK o_sp0 o_FP o_ly o_S o_W0 o_mem0 o_md0 o_own o_lyc o_Sc o_W o_memc o_mdc o_k
  o_regs o_ch o_ps o_n o_b o_M o_C o_cid o_pos] in *.
destruct HPRE as (HJc & _).
pose proof HJ as (HAR3 & _ & _ & _ & _ & Hfrs3 & _).
pose proof HJc as (_ & _ & _ & _ & _ & Hfrsc & _).
destruct (pm_ly_F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [EFA3 _].
destruct (pm_ly_F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as [EFAc _].
assert (EFA : forall c q, frame_addr ly3 c q = frame_addr lyc c q) by (intros c q; rewrite EFA3, EFAc; reflexivity).
clear EFA3 EFAc.
unfold OP_CID in *.
assert (Hfrs : frames S3 = (1, fpos) :: frames Sc) by (rewrite Hfrs3, Hfrsc; reflexivity).
assert (Hin3 : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 1 fpos HAR3 Hin3) as (HF4096 & HFceil & HFapp).
pose proof (frame_al64 SEGS B ly3 S3 W3 mem3 md3 1 fpos HAR3 Hin3) as (HFa64 & _ & _).
rewrite EFA in HF4096, HFceil, HFapp, HFa64.
set (F := frame_addr lyc 1 fpos) in *.
change (fs_frame_bytes 1) with 128 in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
destruct (pm_div8 F HFa64) as [EF8 EF64].
assert (HFr : 0 <= F / 64) by (apply Z.div_pos; lia).
split; [unfold SHADOW_OFF in Ha; lia|]. split.
{ destruct Ha as [Ha | Ha].
  - exact (frm_img SEGS B LAWS ly3 S3 W3 mem3 md3 1 fpos a HAR3 Hin3 ltac:(rewrite EFA; change (fs_frame_bytes 1) with 128; fold F; lia)).
  - intros Hi. pose proof (pa_segs_low a Hi). unfold SHADOW_OFF, kLowMemEnd in *. lia. }
split.
{ intros b0 m0 Hb Hr.
  destruct (al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 b0 m0 HAR3 Hb) as (_ & Hb4096 & Hbceil & Hbia & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbia.
  destruct Ha as [Ha | Ha].
  - pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 md3 b0 m0 1 fpos HAR3 Hb Hin3) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. rewrite EFA in D. change (fs_frame_bytes 1) with 128 in D. fold F in D. lia.
  - unfold SHADOW_OFF in Ha. lia. }
intros c q Hcq.
assert (Hcq3 : In (c, q) (frames S3)) by (rewrite Hfrs; right; exact Hcq).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 c q HAR3 Hcq3) as (Hc4096 & Hcceil & Hcapp).
pose proof (frame_al64 SEGS B ly3 S3 W3 mem3 md3 c q HAR3 Hcq3) as (Hca64 & Hcb64 & Hcb).
rewrite EFA in Hc4096, Hcceil, Hcapp, Hca64.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hcapp.
destruct (in_split _ _ Hcq) as (l2 & l3 & El).
pose proof (sep_frames_pos SEGS B LAWS ly3 S3 W3 mem3 md3 (1, fpos) (c, q) [] l2 l3 HAR3
  ltac:(rewrite Hfrs, El; reflexivity)) as D.
unfold zdisjoint, frame_rng in D. cbn [fst snd] in D. rewrite !EFA in D. change (fs_frame_bytes 1) with 128 in D. fold F in D.
set (Fc := frame_addr lyc c q) in *. set (nc := fs_frame_bytes c) in *.
destruct (pm_div8 Fc Hca64) as [EFc8 EFc64].
destruct (pm_div8 nc Hcb64) as [Enc8 Enc64].
assert (HFcr : 0 <= Fc / 64) by (apply Z.div_pos; lia).
assert (Hncr : 1 <= nc / 64) by lia.
unfold frame_rng, in_zr, shadow_addr. cbn [fst snd]. fold Fc nc.
destruct Ha as [Ha | Ha]; unfold SHADOW_OFF in *.
- split; lia.
- split; [lia|]. rewrite EFc8, Enc8, EF8 in *. lia.
Qed.

(* The kept clauses survive a run that writes only addresses in Zs (PcapSourceOpenB.v:664-698). *)
Lemma pm_topen_kept_upd : forall lyc Sc W memc mdc W2 m2 m2' slo shi (Ek Zs : Z -> Prop),
  AR SEGS B lyc Sc W memc mdc ->
  topen_kept SK SEGS B lyc Sc W memc W2 m2 slo shi Ek ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS (w_H W2) m2' a = aview SEGS (w_H W2) m2 a) ->
  (forall a, Zs a -> a < alloc_ceiling /\ ~ in_img SEGS a /\
     (forall b m, In (b, m) (ablocks B lyc Sc) -> b <= a < b + req_size m -> Ek a) /\
     (forall cid pos, In (cid, pos) (frames Sc) ->
        (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
        Ek a)) ->
  (forall a, slo <= a < shi -> apresent (w_H W2) m2' a) ->
  topen_kept SK SEGS B lyc Sc W memc W2 m2' slo shi Ek.
Proof.
intros lyc Sc W memc mdc W2 m2 m2' slo shi Ek Zs HAR (K1 & K2 & K3 & K4 & K5 & K6) UN HZ Hp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (NZc : forall a, alloc_ceiling <= a -> ~ Zs a) by (intros a Ha HZa; pose proof (proj1 (HZ a HZa)); lia).
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hn. rewrite UN by (first [lia | exact (NZc a ltac:(lia))]). exact (K1 a Ha Hn).
- intros b0 m0 i Hb Hi HnE.
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b0 m0 HAR Hb) as (_ & Hb4096 & Hbceil & _).
  rewrite UN; [exact (K2 b0 m0 i Hb Hi HnE) | lia |].
  intros HZa. apply HnE. exact (proj1 (proj2 (proj2 (HZ _ HZa))) b0 m0 Hb ltac:(lia)).
- intros a Hi Hno He Hof. pose proof (pa_segs_low a Hi) as Hr. unfold kLowMemEnd in Hr.
  rewrite UN; [exact (K3 a Hi Hno He Hof) | lia |]. intros HZa. exact (proj1 (proj2 (HZ a HZa)) Hi).
- intros cid pos a Hin Hr HnE.
  destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hg4096 & Hgceil & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hnn.
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(lia)) as Hsb1.
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(lia)) as Hsb2.
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hnn) as Hse.
  rewrite UN; [exact (K4 cid pos a Hin Hr HnE) | unfold frame_rng, in_zr in Hr; cbn [fst snd] in Hr; destruct Hr; lia |].
  intros HZa. exact (HnE (proj2 (proj2 (proj2 (HZ a HZa))) cid pos Hin Hr)).
- intros a Ha Hn Hpa. eapply (apresent_transfer SEGS); [lia | intros Him; pose proof (pa_segs_low a Him); lia | | exact (K5 a Ha Hn Hpa)].
  apply UN; [lia | exact (NZc a ltac:(lia))].
- exact Hp.
Qed.

Lemma pm_topen_kept_weak : forall lyc Sc W memc W2 mem2 slo shi (Ek : Z -> Prop),
  topen_kept SK SEGS B lyc Sc W memc W2 mem2 slo shi (fun _ => False) ->
  topen_kept SK SEGS B lyc Sc W memc W2 mem2 slo shi Ek.
Proof.
intros lyc Sc W memc W2 mem2 slo shi Ek (K1 & K2 & K3 & K4 & K5 & K6).
split; [exact K1|]. split; [intros b0 m0 i Hb Hi _; exact (K2 b0 m0 i Hb Hi (fun H => H))|].
split; [exact K3|]. split; [intros c q a Hin Hr _; exact (K4 c q a Hin Hr (fun H => H))|]. split; [exact K5 | exact K6].
Qed.

(* The kept clauses across a call that keeps, against the call state, every byte outside its window [lo, hi) and
   the bytes Er (rread_kept, lib/A/Stdio/PFreadM.v:344-360). *)
Lemma pm_topen_kept_rk : forall lyc Sc W memc ly2 S2 W2 mem2 W3 mem3 slo shi lo hi (Ek Er : Z -> Prop),
  topen_kept SK SEGS B lyc Sc W memc W2 mem2 slo shi Ek ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ Er a ->
     aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  (forall b m i, In (b, m) (ablocks B ly2 S2) -> 0 <= i < req_size m -> ~ Er (b + i) ->
     aview SEGS (w_H W3) mem3 (b + i) = aview SEGS (w_H W2) mem2 (b + i)) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  (forall cid pos a, In (cid, pos) (frames S2) ->
     (in_zr a (frame_rng ly2 (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly2 cid pos), fs_frame_bytes cid / 8)) ->
     ~ Er a -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> apresent (w_H W2) mem2 a -> apresent (w_H W3) mem3 a) ->
  slo <= lo -> hi <= shi ->
  (forall a, Er a -> a < alloc_ceiling) ->
  (forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2)) ->
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ Er (b + i)) ->
  (forall c q, In (c, q) (frames Sc) -> In (c, q) (frames S2)) ->
  (forall c q, frame_addr ly2 c q = frame_addr lyc c q) ->
  (forall c q a, In (c, q) (frames Sc) ->
     (in_zr a (frame_rng lyc (c, q)) \/ in_zr a (shadow_addr (frame_addr lyc c q), fs_frame_bytes c / 8)) -> ~ Er a) ->
  (forall a, slo <= a < shi -> apresent (w_H W3) mem3 a) ->
  topen_kept SK SEGS B lyc Sc W memc W3 mem3 slo shi Ek.
Proof.
intros lyc Sc W memc ly2 S2 W2 mem2 W3 mem3 slo shi lo hi Ek Er (K1 & K2 & K3 & K4 & K5 & K6) R1 R2 R3 R4 R5
  Hlo Hhi HEr Hbl HbE Hfr EFA HfE Hp.
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hn. rewrite R1; [exact (K1 a Ha Hn) | lia | lia | intros HE; pose proof (HEr a HE); lia].
- intros b0 m0 i Hb Hi HnE. rewrite (R2 b0 m0 i (Hbl b0 m0 Hb) Hi (HbE b0 m0 i Hb Hi)). exact (K2 b0 m0 i Hb Hi HnE).
- intros a Hi Hno He Hof. rewrite (R3 a Hi Hno He). exact (K3 a Hi Hno He Hof).
- intros cid pos a Hin Hr HnE. rewrite (R4 cid pos a (Hfr cid pos Hin)); [exact (K4 cid pos a Hin Hr HnE) | |].
  + unfold frame_rng in *. rewrite !EFA. exact Hr.
  + exact (HfE cid pos a Hin Hr).
- intros a Ha Hn Hpa. apply R5; [exact Ha | lia | exact (K5 a Ha Hn Hpa)].
- exact Hp.
Qed.

(* The meta invariant between two states of the same journal: its pointer cell is the AR's, its two image words
   and its region are kept from the journal's start by both (YCbq.v:359-360, 367-368). *)
Lemma pm_meta_between : forall STK sp0 FP ly S W0 mem0 md0 own1 ly1 S1 W1 mem1 md1 k1 own2 ly2 S2 W2 mem2 md2 k2 M,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own1 ly1 S1 W1 mem1 md1 k1 ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own2 ly2 S2 W2 mem2 md2 k2 ->
  asrc_meta_inv SEGS K ly1 (rdW W1 mem1) M -> asrc_meta_inv SEGS K ly2 (rdW W2 mem2) M.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own1 ly1 S1 W1 mem1 md1 k1 own2 ly2 S2 W2 mem2 md2 k2 M HJ1 HJ2
  (HX & Himg & Hp & Hm & H0 & H47 & Hal & HZ).
pose proof HJ1 as (HAR1 & Hly1 & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _ & _ & _ & _ & F5 & _).
pose proof HJ2 as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & G3 & _ & _ & _ & _ & G5 & _).
pose proof Hly1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E1 & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E2 & _).
assert (HX0 : In (M, AMETA_SIZE) (ly_extra ly)) by (rewrite <- E1; exact HX).
split; [rewrite E2; exact HX0|]. split; [exact Himg|].
split; [exact (asrc_meta_ptr_of_AR SK SEGS B K ASIL _ _ _ _ _ HAR2)|]. split.
- eapply pm_vm_frame; [|exact Hm]. intros x Hx. cbn in Hx. apply (mbyte_of_aview SEGS).
  destruct (asil_meta _ _ _ _ ASIL x ltac:(lia)) as (Hi & Hns & He & Hlt).
  rewrite (G3 x Hi Hns He ltac:(apply fp_spares_below; exact Hlt)), (F3 x Hi Hns He ltac:(apply fp_spares_below; exact Hlt)).
  reflexivity.
- split; [exact H0|]. split; [exact H47|]. split; [exact Hal|].
  intros a Ha. rewrite <- (HZ a Ha). apply (mbyte_of_aview SEGS).
  assert (HXa : Exists (in_zr a) (ly_extra ly))
    by (apply Exists_exists; exists (M, AMETA_SIZE); split; [exact HX0 | unfold in_zr; cbn [fst snd]; lia]).
  assert (He : ~ (as_errno B <= a < as_errno B + 4)).
  { intros He. pose proof (asil_errno_img _ _ _ _ ASIL a He) as Hi.
    destruct (AR_extra_law_ok SEGS B ly1 S1 W1 mem1 md1 a HAR1 ltac:(rewrite E1; exact HXa)) as (_ & _ & _ & _ & Hni & _).
    exact (Hni Hi). }
  rewrite (G5 a HXa He), (F5 a HXa He). reflexivity.
Qed.

(* The read-only bytes are image bytes (pa_relro_img), so a state that keeps the image keeps them. *)
Lemma pm_rodata_frame : forall (rd rd' : Z -> option Z),
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) -> rd' a = rd a) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B rd -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rd'.
Proof.
intros rd rd' Hk HR a Hro Ho He.
assert (Hi : in_img SEGS a) by (destruct Hro as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)]).
rewrite (Hk a Hi Ho He). exact (HR a Hro Ho He).
Qed.

Lemma pm_last_notin : forall ly3 S3 W3 mem3 md3 l x, AR SEGS B ly3 S3 W3 mem3 md3 ->
  ablocks B ly3 S3 = l ++ [x] -> 0 < req_size (snd x) -> ~ In x l.
Proof.
intros ly3 S3 W3 mem3 md3 l x HAR Hab Hpos Hin. destruct (in_split _ _ Hin) as (l1 & l2 & El).
pose proof (sep_blocks_pos SEGS B LAWS ly3 S3 W3 mem3 md3 x x l1 l2 [] HAR ltac:(rewrite Hab, El, <- app_assoc; reflexivity)) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. lia.
Qed.

Lemma pm_shent_ok : forall Ex (m : word -> option byte) ps,
  U Ex pm_Bx = SHADOW_OFF -> U Ex (SOff 19 0) = ps ->
  (4096 <= ps /\ (ps + 24 <= kLowShadowBeg \/ kHighMemBeg <= ps)) ->
  range_addressable (YCbn.rd_of SEGS m) SHADOW_OFF ps 24 ->
  sh_ok SEGS pm_Bx pm_SH Ex m.
Proof.
intros Ex m ps HB Hq Hz HR. unfold sh_ok, pm_SH. apply Forall_cons; [|apply Forall_nil].
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hq. split.
- rewrite Z.add_0_r. exact HR.
- intros a Ha. cbn in Ha. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

Lemma pm_shok_transfer : forall E E' (m m' : word -> option byte) ps,
  sh_ok SEGS pm_Bx pm_SH E m -> U E' pm_Bx = U E pm_Bx -> U E' (SOff 19 0) = U E (SOff 19 0) -> U E (SOff 19 0) = ps ->
  U E pm_Bx = SHADOW_OFF ->
  (forall x, ps <= x < ps + 24 -> YCbn.rd_of SEGS m' (SHADOW_OFF + x / 8) = YCbn.rd_of SEGS m (SHADOW_OFF + x / 8)) ->
  sh_ok SEGS pm_Bx pm_SH E' m'.
Proof.
intros E E' m m' ps HS EB E19 U19 UB Hk. unfold sh_ok, pm_SH in *. apply Forall_inv in HS.
apply Forall_cons; [|apply Forall_nil].
destruct HS as [HR HA]. unfold shent_ok, app_apart in *. cbn [she_m she_lo she_hi] in *. rewrite EB, E19. split; [|exact HA].
rewrite UB, U19 in HR |- *. apply (pm_ra_frame _ _ _ _ HR). intros x Hx. unfold shadow_of_addr. apply Hk. lia.
Qed.

(* ---- the symbolic state at the fopen return (0x812f8) --------------------------------------------------------- *)
Lemma pm_entry : forall (cx : ocx) fpos h ly2 S2 W2 (ms : machine_state) md,
  op_pre SK B K MT FM_RA CTX roimg cx -> op_fopen_ret SK B K MT cx fpos h ly2 S2 W2 ms md ->
  st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs ms) pm_extra)) (ss_pm OP_RET_FOPEN) (restrict (w_H W2) ms) /\
  sh_ok SEGS pm_Bx pm_SH (Eimg (Ereg (ms_regs ms) pm_extra)) (mrestrict (w_H W2) (ms_mem ms)).
Proof.
intros cx fpos h ly2 S2 W2 ms md HPRE HFR.
destruct cx as [STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k regs ch ps n b M C cid pos].
unfold op_fopen_ret, oSH, oFL, oF, op_pre, osp1 in *. cbn [o_STK o_sp0 o_FP o_ly o_S o_W0 o_mem0 o_md0 o_own o_lyc o_Sc o_W
  o_memc o_mdc o_k o_regs o_ch o_ps o_n o_b o_M o_C o_cid o_pos] in *.
pm_unpack_fr HFR.
destruct HPRE as (HJc & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & _ & _ & Hown & Hfa1 & Hfa2 & _ & Hps8 & _).
pose proof HJc as (HAR & _ & _ & _ & _ & Hfrsc & _).
destruct (pm_ly_F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [EFA2 _].
destruct (pm_ly_F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as [EFAc _].
assert (EFA : forall c q, frame_addr ly2 c q = frame_addr lyc c q) by (intros c q; rewrite EFA2, EFAc; reflexivity).
clear EFA2 EFAc.
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrsc; apply in_or_app; left; exact Hown).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hc4096 & Hcceil & Hcapp).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hcapp.
set (E := Eimg (Ereg (ms_regs ms) pm_extra)).
assert (EL : forall nn, (nn < A_TEXT)%nat -> ew E nn = ew (Ereg (ms_regs ms) pm_extra) nn)
  by (intros nn Hn; subst E; apply Eimg_low; exact Hn).
assert (ER : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> (nn < 32)%nat -> ew E nn = getr (ms_regs ms) r)
  by (intros nn r Hr Hn; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hr).
assert (E19 : ew E 19 = w64 ps) by (rewrite (ER 19%nat 19%bv eq_refl) by lia; exact R19).
assert (E32 : ew E 32 = w64 pm_SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms) pm_extra 0)).
assert (U19 : bv_unsigned (ew E 19) = ps) by (rewrite E19; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = pm_SB) by (rewrite E32; apply unsigned_lit_small; unfold pm_SB; lia).
assert (HPS : forall a, ps <= a < ps + 24 -> apresent (w_H W2) (ms_mem ms) a).
{ intros a Ha. refine (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ _)).
  right. right. right. exists cid, pos. split; [right; exact Hown|]. left. unfold in_zr. cbn [fst snd]. rewrite EFA. lia. }
split.
- unfold ss_pm, pm_sr.
  apply (ast_ok_pi_set_reg_fp E (mkSS OP_RET_FOPEN sr_atoms [r_pmA; r_pmB] None pm_facts) _ 23%bv (SOff 32 0));
    [| vm_compute; reflexivity | cbn [sv_denot ms_regs restrict]; rewrite E32, R23; reflexivity].
  apply pm_mid_st_ok; [exact Hfr | exact Hpc | exact Hsvc | exact Hrv | exact Hfcsr | exact Hrom
    | apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | | | ].
  + unfold r_pmA, r_pmB.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite U19. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply HPS. lia.
    * rewrite U19. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply HPS. lia.
  + apply pairwise_disjoint_of_extents. unfold r_pmA, r_pmB, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U19.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. clear. repeat split; lia.
  + split; [|split; exact I]. cbn [pm_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
    rewrite U19, U32. change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r.
    unfold pm_SB. revert C1 Hc4096 Hcceil Hfa1 Hfa2 Hps8. clear. intros.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
- apply (pm_shent_ok _ _ ps).
  + unfold pm_Bx. rewrite (U_atom _ 32 pm_SB E32) by (unfold pm_SB; lia). reflexivity.
  + rewrite (U_atom _ 19 ps E19) by lia. reflexivity.
  + unfold kLowShadowBeg. lia.
  + rewrite <- (aview_rd_of SEGS). exact HRA.
Qed.

(* ---- the cut of the empty input (0x813f8) ----------------------------------------------------------------- *)
Lemma pm_null_cut : forall (cx : ocx) fpos ly2 S2 W2 (ms ms3 : machine_state) md md3,
  op_pre SK B K MT FM_RA CTX roimg cx ->
  op_fopen_ret SK B K MT cx fpos 0 ly2 S2 W2 ms md ->
  o_n cx = 0 ->
  ms_pc_val ms3 = w64 (BASE + OP_CUT_NULL) ->
  ms_resv ms3 = None -> ms_svc_pending ms3 = None -> ms_rom ms3 = seg_rom SEGS ->
  ms_fregs ms3 = fp_regs -> ms_fcsr ms3 = fp_csr ->
  ajournal SEGS B (o_STK cx) (o_sp0 cx) (o_FP cx) (o_ly cx) (o_S cx) (o_W0 cx) (o_mem0 cx) (o_md0 cx)
    ((OP_CID, fpos) :: o_own cx) ly2 S2 W2 (ms_mem ms3) md3 (o_k cx + EV_FUZZ_FOPEN) ->
  (forall r, In r pm_keepN -> getr (ms_regs ms3) r = getr (ms_regs ms) r) ->
  getr (ms_regs ms3) 23%bv = w64 SHADOW_OFF ->
  getr (ms_regs ms3) 24%bv = w64 (SHADOW_OFF + o_ps cx / 8) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ ((o_ps cx <= a < o_ps cx + 8) \/ (o_ps cx + 12 <= a < o_ps cx + 22)) ->
     aview SEGS (w_H W2) (ms_mem ms3) a = aview SEGS (w_H W2) (ms_mem ms) a) ->
  val_mem SEGS (rdW W2 (ms_mem ms3)) (o_ps cx) 8 0 -> val_mem SEGS (rdW W2 (ms_mem ms3)) (o_ps cx + 12) 4 0 ->
  val_mem SEGS (rdW W2 (ms_mem ms3)) (o_ps cx + 16) 4 0 -> val_mem SEGS (rdW W2 (ms_mem ms3)) (o_ps cx + 20) 2 0 ->
  m_fds md3 = m_fds md -> m_fs md3 = m_fs md ->
  op_gi_null SK B K MT cx fpos ly2 S2 W2 ms3 md3.
Proof.
intros cx fpos ly2 S2 W2 ms ms3 md md3 HPRE HFR Hnz Hpc3 Hrv3 Hsv3 Hrom3 Hfr3 Hfc3 HJ3 REG Q23 Q24 UN V0 V12 V16 V20
  Hfd3 Hfs3.
destruct cx as [STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k regs ch ps n b M C cid pos].
unfold op_gi_null, op_mid, op_fopen_ret, oSH, oFL, oF, op_pre, osp1, OP_FLAGPTR in *.
cbn [o_STK o_sp0 o_FP o_ly o_S o_W0 o_mem0 o_md0 o_own o_lyc o_Sc o_W o_memc o_mdc o_k
  o_regs o_ch o_ps o_n o_b o_M o_C o_cid o_pos] in *.
pm_unpack_fr HFR.
destruct HPRE as (HJc & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & _ & _ & Hown & Hfa1 & Hfa2 & _ & Hps8 & _).
destruct (Hn0 Hnz) as (_ & Hab & Hnone & Hmo). clear Hn0 Hn1.
pose proof HJc as (HAR & _ & _ & _ & _ & Hfrsc & _).
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
destruct (pm_ly_F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [EFA2 _].
destruct (pm_ly_F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as [EFAc _].
assert (EFA : forall c q, frame_addr ly2 c q = frame_addr lyc c q) by (intros c q; rewrite EFA2, EFAc; reflexivity).
clear EFA2 EFAc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TPCAP_SOURCE_OPEN_STK = 18736) by reflexivity.
unfold OP_CID in *.
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrsc; apply in_or_app; left; exact Hown).
assert (HinF : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hc4096 & Hcceil & Hcapp).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 (ms_mem ms) md 1 fpos HAR2 HinF) as (HF4096 & HFceil & HFapp).
pose proof (frame_al64 SEGS B ly2 S2 W2 (ms_mem ms) md 1 fpos HAR2 HinF) as (HFa64 & _ & _).
rewrite EFA in HF4096, HFceil, HFapp, HFa64.
destruct (in_split _ _ Hin) as (l2 & l3 & El).
pose proof (sep_frames_pos SEGS B LAWS ly2 S2 W2 (ms_mem ms) md (1, fpos) (cid, pos) [] l2 l3 HAR2
  ltac:(rewrite Hfrs2, El; reflexivity)) as DFc.
unfold zdisjoint, frame_rng in DFc. cbn [fst snd] in DFc. rewrite !EFA in DFc.
set (F := frame_addr lyc 1 fpos) in *.
change (fs_frame_bytes 1) with 128 in *.
set (sp1 := 32 * ((spZ regs - OPEN_FRAME) / 32)) in *.
assert (Hsp64 : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply u64_range).
destruct (pm_osp1_facts (spZ regs) ltac:(lia) Hal16) as (Hsp1r & Hsp1al).
change OPEN_FRAME with 96 in sp1. fold sp1 in Hsp1r, Hsp1al.
assert (Hsp_lo : alloc_ceiling + 18736 <= spZ regs) by lia.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hcapp, HFapp.
destruct (pm_div8 F HFa64) as [EF8 EF64].
assert (HF8b : 0 <= F / 8 /\ F / 8 + 16 <= 2 ^ 44) by (rewrite EF8; lia).
assert (HIE : pcap_img_end = (symaddr ImgPages.AsanUbsan.top)) by reflexivity.
split; [exact Hpc3|].
split.
2: { split; [exact Hnz|]. split; [exact Hab|]. split; [|exact Hmo].
     apply (pm_asource_none_frame K (rdW W2 (ms_mem ms))); [|exact Hnone].
     intros a Ha. apply (mbyte_of_aview SEGS). pose proof (pm_src_env_img a Ha) as Hk.
     destruct (asil_env _ _ _ _ ASIL a Ha) as [Hi _].
     apply UN; [lia | intros [Hp|Hp]; exact (frm_img SEGS B LAWS lyc Sc W memc mdc cid pos a HAR Hin ltac:(lia) Hi)]. }
split; [exact Hrv3|]. split; [exact Hsv3|]. split; [exact Hrom3|]. split; [exact Hfr3|]. split; [exact Hfc3|].
split; [exact HJ3|].
split; [lia|].
split; [unfold EV_FUZZ_FOPEN in Hnev2; exact Hnev2|].
split; [exact Hfrs2|]. split; [exact Hnin2|]. split; [exact HfsS2|].
split; [rewrite (REG 2%bv) by (cbn; tauto); exact R2|].
split; [rewrite (REG 8%bv) by (cbn; tauto); exact R8|].
split; [rewrite (REG 9%bv) by (cbn; tauto); exact R9|].
split; [rewrite (REG 18%bv) by (cbn; tauto); exact R18|].
split; [rewrite (REG 19%bv) by (cbn; tauto); exact R19|].
split; [rewrite (REG 20%bv) by (cbn; tauto); exact R20|].
split; [rewrite (REG 21%bv) by (cbn; tauto); exact R21|].
split; [rewrite (REG 22%bv) by (cbn; tauto); exact R22|].
split; [exact Q23|]. split; [exact Q24|].
split; [rewrite (REG 25%bv) by (cbn; tauto); rewrite R25; symmetry; apply pm_w64_unsigned|].
split; [rewrite (REG 3%bv) by (cbn; tauto); exact R3|].
split; [rewrite (REG 4%bv) by (cbn; tauto); exact R4|].
split; [rewrite (REG 26%bv) by (cbn; tauto); exact R26|].
split; [rewrite (REG 27%bv) by (cbn; tauto); exact R27|].
split; [rewrite (pm_rdword_agree (aview SEGS (w_H W2) (ms_mem ms))); [exact Hra | intros i Hi; apply UN; lia]|].
split; [intros j Hj; rewrite (pm_rdword_agree (aview SEGS (w_H W2) (ms_mem ms)));
        [exact (Hsav j Hj) | intros i Hi; apply UN; lia]|].
split; [rewrite (pm_rdword_agree (aview SEGS (w_H W2) (ms_mem ms))); [exact HMG | intros i Hi; apply UN; lia]|].
split; [rewrite (pm_rdword_agree (aview SEGS (w_H W2) (ms_mem ms))); [exact HO8 | intros i Hi; apply UN; lia]|].
split; [rewrite (pm_rdword_agree (aview SEGS (w_H W2) (ms_mem ms))); [exact HO16 | intros i Hi; apply UN; lia]|].
split; [rewrite (pm_rdword_agree (aview SEGS (w_H W2) (ms_mem ms))); [exact HFLP | intros i Hi; apply UN; lia]|].
split; [reflexivity|].
split; [intros i Hi; rewrite UN; [exact (Hsh i Hi) | unfold SHADOW_OFF; lia | unfold SHADOW_OFF; lia]|].
split; [exact V0|]. split; [exact V12|]. split; [exact V16|]. split; [exact V20|].
split; [intros i Hi; rewrite UN by lia; exact (HPS0 i ltac:(lia))|].
split.
{ assert (HK0 : topen_kept SK SEGS B lyc Sc W memc W2 (ms_mem ms) (spZ regs - TPCAP_SOURCE_OPEN_STK) (spZ regs)
                  (fun a => ps <= a < ps + 22)) by (apply pm_topen_kept_weak; exact HKEPT).
  apply (pm_topen_kept_upd lyc Sc W memc mdc W2 (ms_mem ms) (ms_mem ms3) _ _ _
    (fun a => (ps <= a < ps + 8) \/ (ps + 12 <= a < ps + 22)) HAR HK0).
  - intros a Ha Hn. exact (UN a Ha Hn).
  - intros a HZa. cbv beta in HZa. split; [lia|].
    split; [exact (frm_img SEGS B LAWS lyc Sc W memc mdc cid pos a HAR Hin ltac:(lia))|].
    split; [intros b0 m0 _ _; cbv beta; lia | intros c q _ _; cbv beta; lia].
  - intros a Ha. apply Hpres3. lia. }
split; [rewrite Hfd3; exact Hfds|]. split; [rewrite Hfs3; exact Hfs|].
split; [eapply pm_meta_between; [exact HJ | exact HJ3 | exact HMETA]|].
split.
{ apply (pm_rodata_frame (aview SEGS (w_H W2) (ms_mem ms))); [|exact HROD].
  intros a Hi Ho He. pose proof (pa_img_range a Hi) as Hr1.
  apply UN; [lia | intros [Hp|Hp]; exact (frm_img SEGS B LAWS lyc Sc W memc mdc cid pos a HAR Hin ltac:(lia) Hi)]. }
eapply achain_kept with (lo := sp1); [exact Hch | lia | lia | intros a Ha; apply UN; lia].
Qed.

(* ---- the fread call (0x81388) ---------------------------------------------------------------------------- *)
Lemma pm_fread_pre : forall (cx : ocx) fpos h ly2 S2 W2 (ms mc : machine_state) md mdc',
  op_pre SK B K MT FM_RA CTX roimg cx ->
  op_fopen_ret SK B K MT cx fpos h ly2 S2 W2 ms md ->
  1 <= o_n cx ->
  ajournal SEGS B (o_STK cx) (o_sp0 cx) (o_FP cx) (o_ly cx) (o_S cx) (o_W0 cx) (o_mem0 cx) (o_md0 cx)
    ((OP_CID, fpos) :: o_own cx) ly2 S2 W2 (ms_mem mc) mdc' (o_k cx + EV_FUZZ_FOPEN) ->
  getr (ms_regs mc) 1%bv = Z_to_bv 64 (BASE + OP_CUT_READ) ->
  (forall r, In r pm_keepR -> getr (ms_regs mc) r = getr (ms_regs ms) r) ->
  getr (ms_regs mc) 10%bv = w64 (oF cx fpos + OP_HDR) -> getr (ms_regs mc) 11%bv = w64 1 ->
  getr (ms_regs mc) 12%bv = w64 24 -> getr (ms_regs mc) 13%bv = w64 h ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ ((o_ps cx <= a < o_ps cx + 8) \/ (o_ps cx + 12 <= a < o_ps cx + 22) \/
       (oSH cx fpos + 4 <= a < oSH cx fpos + 7)) ->
     aview SEGS (w_H W2) (ms_mem mc) a = aview SEGS (w_H W2) (ms_mem ms) a) ->
  (forall i, 4 <= i < 7 -> aview SEGS (w_H W2) (ms_mem mc) (oSH cx fpos + i) = Some 0) ->
  afread_pre SK SEGS B K (o_STK cx) (o_sp0 cx) (o_FP cx) (o_ly cx) (o_S cx) (o_W0 cx) (o_mem0 cx) (o_md0 cx)
    ((OP_CID, fpos) :: o_own cx) ly2 S2 W2 (ms_mem mc) mdc' (o_k cx + EV_FUZZ_FOPEN) (ms_regs mc)
    ((spZ (o_regs cx), raZ (o_regs cx), s0Z (o_regs cx)) :: o_ch cx) (oF cx fpos + OP_HDR) 24 h (o_b cx) 0 (o_C cx).
Proof.
intros cx fpos h ly2 S2 W2 ms mc md mdc' HPRE HFR Hn1' HJc' Q1 QK Q10 Q11 Q12 Q13 UNc SHc.
destruct cx as [STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k regs ch ps n b M C cid pos].
unfold afread_pre, rread_call, rread_wr_ok, rread_dest, rread_at, op_fopen_ret, oSH, oFL, oF, op_pre, osp1, OP_HDR in *.
cbn [o_STK o_sp0 o_FP o_ly o_S o_W0 o_mem0 o_md0 o_own o_lyc o_Sc o_W o_memc o_mdc o_k
  o_regs o_ch o_ps o_n o_b o_M o_C o_cid o_pos] in *.
pm_unpack_fr HFR.
destruct HPRE as (HJc & _ & _ & _ & Hgp & Htp & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & _ & _ & Hown & Hfa1 & Hfa2 & _ & Hps8 &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & HnC & _ & Hinput & _).
destruct (Hn1 Hn1') as (Hh4096 & Hh16 & Hab & Hunb & Hmo & HFP). clear Hn0 Hn1.
destruct (Hinput Hn1') as (Hinb0 & _ & _).
pose proof HJc as (HAR & _ & _ & _ & _ & Hfrsc & _).
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
destruct (pm_ly_F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [EFA2 _].
destruct (pm_ly_F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as [EFAc _].
assert (EFA : forall c q, frame_addr ly2 c q = frame_addr lyc c q) by (intros c q; rewrite EFA2, EFAc; reflexivity).
clear EFA2 EFAc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TPCAP_SOURCE_OPEN_STK = 18736) by reflexivity.
pose proof (pa_base_lo (PL := PL_pcap) (PI := PI)) as HBLO. pose proof (@pa_B_ok _ _ PI) as HBOK.
unfold OP_CID in *.
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrsc; apply in_or_app; left; exact Hown).
assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; right; exact Hin).
assert (HinF : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hc4096 & Hcceil & Hcapp).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 (ms_mem ms) md 1 fpos HAR2 HinF) as (HF4096 & HFceil & HFapp).
pose proof (frame_al64 SEGS B ly2 S2 W2 (ms_mem ms) md 1 fpos HAR2 HinF) as (HFa64 & _ & _).
rewrite EFA in HF4096, HFceil, HFapp, HFa64.
destruct (in_split _ _ Hin) as (l2 & l3 & El).
pose proof (sep_frames_pos SEGS B LAWS ly2 S2 W2 (ms_mem ms) md (1, fpos) (cid, pos) [] l2 l3 HAR2
  ltac:(rewrite Hfrs2, El; reflexivity)) as DFc.
unfold zdisjoint, frame_rng in DFc. cbn [fst snd] in DFc. rewrite !EFA in DFc.
assert (Hfin : In (h, SRC_FILE_BLOCK) (ablocks B ly2 S2)) by (rewrite Hab; apply in_or_app; right; left; reflexivity).
assert (Hbin : In (b, Z.of_nat (length C)) (ablocks B ly2 S2))
  by (rewrite Hab; apply in_or_app; left; rewrite <- HnC; exact Hinb0).
destruct (al_blocks _ _ LAWS ly2 S2 W2 (ms_mem ms) md h SRC_FILE_BLOCK HAR2 Hfin) as (_ & _ & Hhceil & Hhia & _).
destruct (al_blocks _ _ LAWS ly2 S2 W2 (ms_mem ms) md b (Z.of_nat (length C)) HAR2 Hbin) as (_ & Hb4096 & Hbceil & Hbia & _).
pose proof (req_size_pos (Z.of_nat (length C)) ltac:(lia)) as [_ Hreqb].
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 (ms_mem ms) md h SRC_FILE_BLOCK 1 fpos HAR2 Hfin HinF) as DhF.
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 (ms_mem ms) md b (Z.of_nat (length C)) 1 fpos HAR2 Hbin HinF) as DbF.
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 (ms_mem ms) md h SRC_FILE_BLOCK cid pos HAR2 Hfin Hin2) as DhP.
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 (ms_mem ms) md b (Z.of_nat (length C)) cid pos HAR2 Hbin Hin2) as DbP.
unfold zdisjoint in DhF, DbF, DhP, DbP. cbn [fst snd] in DhF, DbF, DhP, DbP. rewrite EFA in DhF, DbF, DhP, DbP.
change (req_size SRC_FILE_BLOCK) with 1304 in *.
set (F := frame_addr lyc 1 fpos) in *.
change (fs_frame_bytes 1) with 128 in *.
set (sp1 := 32 * ((spZ regs - OPEN_FRAME) / 32)) in *.
assert (Hsp64 : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply u64_range).
destruct (pm_osp1_facts (spZ regs) ltac:(lia) Hal16) as (Hsp1r & Hsp1al).
change OPEN_FRAME with 96 in sp1. fold sp1 in Hsp1r, Hsp1al.
assert (Hsp_lo : alloc_ceiling + 18736 <= spZ regs) by lia.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hcapp, HFapp, Hhia, Hbia.
destruct (pm_div8 F HFa64) as [EF8 EF64].
assert (HF8b : 0 <= F / 8 /\ F / 8 + 16 <= 2 ^ 44) by (rewrite EF8; lia).
assert (HIE : pcap_img_end = (symaddr ImgPages.AsanUbsan.top)) by reflexivity.
(* The separations the goals below need, each from the one disjunction it uses; then the disjunctions go, so
   that lia does not case-split on all of them at every side condition. *)
assert (O_hi : forall a, sp1 <= a < 2 ^ 64 -> ~ ((ps <= a < ps + 8) \/ (ps + 12 <= a < ps + 22) \/
  (SHADOW_OFF + F / 8 + 4 <= a < SHADOW_OFF + F / 8 + 7)))
  by (intros a Ha; clear - Ha Hsp1r Hsp_lo Hcceil Hfa2 HF8b C1; unfold SHADOW_OFF; lia).
assert (O_h : forall a, h <= a < h + 1304 -> ~ ((ps <= a < ps + 8) \/ (ps + 12 <= a < ps + 22) \/
  (SHADOW_OFF + F / 8 + 4 <= a < SHADOW_OFF + F / 8 + 7)))
  by (intros a Ha; clear - Ha DhP Hfa1 Hfa2 Hhia HF8b; unfold SHADOW_OFF; lia).
assert (O_b : forall a, b <= a < b + Z.of_nat (length C) -> ~ ((ps <= a < ps + 8) \/ (ps + 12 <= a < ps + 22) \/
  (SHADOW_OFF + F / 8 + 4 <= a < SHADOW_OFF + F / 8 + 7)))
  by (intros a Ha; clear - Ha DbP Hfa1 Hfa2 Hbia HF8b Hreqb; unfold SHADOW_OFF; lia).
assert (O_img : forall a, in_img SEGS a -> ~ ((ps <= a < ps + 8) \/ (ps + 12 <= a < ps + 22) \/
  (SHADOW_OFF + F / 8 + 4 <= a < SHADOW_OFF + F / 8 + 7))).
{ intros a Hi. pose proof (pa_img_range a Hi) as Hr1. intros [Hp|[Hp|Hp]].
  - exact (frm_img SEGS B LAWS lyc Sc W memc mdc cid pos a HAR Hin ltac:(clear - Hp Hfa1 Hfa2; lia) Hi).
  - exact (frm_img SEGS B LAWS lyc Sc W memc mdc cid pos a HAR Hin ltac:(clear - Hp Hfa1 Hfa2; lia) Hi).
  - clear - Hp Hr1 HIE HF8b. unfold SHADOW_OFF in Hp. lia. }
assert (O_SH : forall i, 0 <= i < 16 -> ~ (4 <= i < 7) -> ~ ((ps <= SHADOW_OFF + F / 8 + i < ps + 8) \/
  (ps + 12 <= SHADOW_OFF + F / 8 + i < ps + 22) \/
  (SHADOW_OFF + F / 8 + 4 <= SHADOW_OFF + F / 8 + i < SHADOW_OFF + F / 8 + 7)))
  by (intros i Hi Hn; clear - Hi Hn Hcapp Hfa1 Hfa2 HF8b; unfold SHADOW_OFF; lia).
assert (DhF' : F + 32 + 24 <= h \/ h + SRC_FILE_BLOCK <= F + 32) by (clear - DhF; unfold SRC_FILE_BLOCK; lia).
assert (DbF' : F + 32 + 24 <= b \/ b + Z.of_nat (length C) <= F + 32) by (clear - DbF Hreqb; lia).
assert (AMR : amem_range (F + 32) 24) by (clear - HFapp HFceil C1; unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg; lia).
clear Hcapp HFapp Hhia Hbia DFc DhF DbF DhP DbP.
assert (Esp : spZ (ms_regs mc) = sp1)
  by (unfold spZ; rewrite (QK 2%bv) by (cbn; tauto); rewrite R2; apply unsigned_lit_small; lia).
assert (Es0 : s0Z (ms_regs mc) = spZ regs)
  by (unfold s0Z; rewrite (QK 8%bv) by (cbn; tauto); rewrite R8; apply unsigned_lit_small; exact Hsp64).
unfold AFREAD_STK. rewrite Esp, Es0.
split.
{ split; [exact HJc'|].
  split; [rewrite Q1; apply ret_ok_codeptr_v; [unfold OP_CUT_READ; lia | reflexivity]|].
  split; [unfold raZ; rewrite Q1, unsigned_lit_small; unfold OP_CUT_READ; lia|].
  split; [rewrite (QK 3%bv) by (cbn; tauto); rewrite R3; exact Hgp|].
  split; [rewrite (QK 4%bv) by (cbn; tauto); rewrite R4; exact Htp|].
  split; [exact Hsp1al|].
  split; [lia|]. split; [lia|].
  eapply achain_kept with (lo := sp1); [exact Hch | lia | lia | intros a Ha; apply UNc; [lia | exact (O_hi a Ha)]]. }
split; [exact Q10|]. split; [exact Q11|]. split; [exact Q12|]. split; [exact Q13|].
split; [exact Hfin|]. split; [exact Hbin|].
split; [left; lia|].
split.
{ apply (pm_asource_at_frame K (rdW W2 (ms_mem ms))); [|exact (proj1 Hunb)].
  intros a Ha. apply (mbyte_of_aview SEGS). unfold SRC_FILE_BLOCK in Ha.
  destruct Ha as [Ha | [Ha | Ha]].
  - apply UNc; [lia | exact (O_h a Ha)].
  - apply UNc; [lia | exact (O_b a Ha)].
  - pose proof (pm_src_env_img a Ha) as Hk. destruct (asil_env _ _ _ _ ASIL a Ha) as [Hi _].
    apply UNc; [lia | exact (O_img a Hi)]. }
split.
{ intros a Ha. unfold SRC_FILE_BLOCK in Ha. split; [|lia].
  assert (HfpA : inFP (asource_fp h) a)
    by (exists (h, h + SRC_FILE_BLOCK); split; [unfold asource_fp; apply in_eq | cbn [fst snd]; unfold SRC_FILE_BLOCK; lia]).
  destruct (HFP a HfpA) as [HF1 | HF2].
  - right. left. split; [exact HF1|]. exists h, SRC_FILE_BLOCK. split; [exact Hfin|].
    change (req_size SRC_FILE_BLOCK) with 1304. lia.
  - right. right. left. exact HF2. }
split; [lia|].
split; [exact DhF'|].
split; [exact DbF'|].
split; [lia|].
split; [exact AMR|].
split.
{ left. exists 1, fpos. split; [exact HinF|]. intros a Ha. unfold frame_rng, in_zr. cbn [fst snd]. rewrite EFA.
  change (fs_frame_bytes 1) with 128. fold F. lia. }
split.
{ intros a Ha. split; [|lia]. right. right. right. exists 1, fpos. split; [left; reflexivity|]. left.
  unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 1) with 128. fold F. lia. }
split.
{ intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
  destruct (pm_hdr_shadow F x HFa64 ltac:(lia)) as [-> Hi]. rewrite Z.add_assoc. exact (SHc _ Hi). }
intros _ s Hs. unfold shadow_addr in Hs. destruct (pm_hull_bounds F HFa64) as [HB1 HB2]. rewrite HB1, HB2 in Hs.
assert (Hs0 : 0 <= s - (SHADOW_OFF + F / 8) < 8) by lia.
replace s with (SHADOW_OFF + F / 8 + (s - (SHADOW_OFF + F / 8))) by lia.
set (i := s - (SHADOW_OFF + F / 8)) in *.
destruct (Z_lt_le_dec i 4) as [Hc|Hc]; [|destruct (Z_lt_le_dec i 7) as [Hc2|Hc2]].
- rewrite UNc by (first [unfold SHADOW_OFF; lia | apply O_SH; lia]).
  replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite (Hsh (Z.to_nat i) ltac:(lia)). discriminate.
- rewrite (SHc i ltac:(lia)). discriminate.
- rewrite UNc by (first [unfold SHADOW_OFF; lia | apply O_SH; lia]).
  replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite (Hsh (Z.to_nat i) ltac:(lia)). discriminate.
Qed.

(* ---- the cut after fread (0x8138c) ------------------------------------------------------------------------- *)
Lemma pm_read_cut : forall (cx : ocx) fpos h ly2 S2 W2 (ms mc : machine_state) md mdc' W3 regs3 mem3 md3,
  op_pre SK B K MT FM_RA CTX roimg cx ->
  op_fopen_ret SK B K MT cx fpos h ly2 S2 W2 ms md ->
  1 <= o_n cx ->
  ajournal SEGS B (o_STK cx) (o_sp0 cx) (o_FP cx) (o_ly cx) (o_S cx) (o_W0 cx) (o_mem0 cx) (o_md0 cx)
    ((OP_CID, fpos) :: o_own cx) ly2 S2 W2 (ms_mem mc) mdc' (o_k cx + EV_FUZZ_FOPEN) ->
  getr (ms_regs mc) 1%bv = Z_to_bv 64 (BASE + OP_CUT_READ) ->
  (forall r, In r pm_keepR -> getr (ms_regs mc) r = getr (ms_regs ms) r) ->
  getr (ms_regs mc) 20%bv = w64 (oF cx fpos + OP_HDR) ->
  getr (ms_regs mc) 23%bv = w64 SHADOW_OFF ->
  getr (ms_regs mc) 24%bv = w64 (SHADOW_OFF + o_ps cx / 8) ->
  getr (ms_regs mc) 25%bv = w64 24 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ ((o_ps cx <= a < o_ps cx + 8) \/ (o_ps cx + 12 <= a < o_ps cx + 22) \/
       (oSH cx fpos + 4 <= a < oSH cx fpos + 7)) ->
     aview SEGS (w_H W2) (ms_mem mc) a = aview SEGS (w_H W2) (ms_mem ms) a) ->
  (forall i, 4 <= i < 7 -> aview SEGS (w_H W2) (ms_mem mc) (oSH cx fpos + i) = Some 0) ->
  val_mem SEGS (rdW W2 (ms_mem mc)) (o_ps cx) 8 h -> val_mem SEGS (rdW W2 (ms_mem mc)) (o_ps cx + 12) 4 0 ->
  val_mem SEGS (rdW W2 (ms_mem mc)) (o_ps cx + 16) 4 0 -> val_mem SEGS (rdW W2 (ms_mem mc)) (o_ps cx + 20) 2 0 ->
  m_fds mdc' = m_fds md -> m_fs mdc' = m_fs md ->
  ajournal SEGS B (o_STK cx) (o_sp0 cx) (o_FP cx) (o_ly cx) (o_S cx) (o_W0 cx) (o_mem0 cx) (o_md0 cx)
    ((OP_CID, fpos) :: o_own cx) ly2 S2 W3 mem3 md3 (o_k cx + EV_FUZZ_FOPEN) ->
  aregs_preserved (ms_regs mc) regs3 ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ (ms_regs mc) - AFREAD_STK <= a < spZ (ms_regs mc)) ->
     ~ rread_wrset h (oF cx fpos + OP_HDR) 24 a -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) (ms_mem mc) a) ->
  (forall b m i, In (b, m) (ablocks B ly2 S2) -> 0 <= i < req_size m -> ~ rread_wrset h (oF cx fpos + OP_HDR) 24 (b + i) ->
     aview SEGS (w_H W3) mem3 (b + i) = aview SEGS (w_H W2) (ms_mem mc) (b + i)) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) (ms_mem mc) a) ->
  (forall cid pos a, In (cid, pos) (frames S2) ->
     (in_zr a (frame_rng ly2 (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly2 cid pos), fs_frame_bytes cid / 8)) ->
     ~ rread_wrset h (oF cx fpos + OP_HDR) 24 a -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) (ms_mem mc) a) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ (ms_regs mc) - AFREAD_STK <= a < spZ (ms_regs mc)) ->
     apresent (w_H W2) (ms_mem mc) a -> apresent (w_H W3) mem3 a) ->
  getr regs3 10%bv = w64 (rread_k 24 (Z.of_nat (length (o_C cx))) 0) ->
  garr8 SEGS (rdW W3 mem3) (oF cx fpos + OP_HDR)
    (firstn (Z.to_nat (rread_k 24 (Z.of_nat (length (o_C cx))) 0)) (skipn (Z.to_nat 0) (o_C cx))) ->
  asource_at SEGS K (rdW W3 mem3) h (o_b cx) (o_C cx) (0 + rread_k 24 (Z.of_nat (length (o_C cx))) 0) ->
  m_fds md3 = m_fds mdc' -> m_fs md3 = m_fs mdc' ->
  op_gi_read SK B K MT cx fpos ly2 S2 W3 (mkst regs3 (getr (ms_regs mc) 1%bv) mem3 (seg_rom SEGS)) md3.
Proof.
intros cx fpos h ly2 S2 W2 ms mc md mdc' W3 regs3 mem3 md3 HPRE HFR Hn1' HJc' Q1 QK Q20 Q23 Q24 Q25 UNc SHc
  V0 V12 V16 V20 Hfdc Hfsc HJ3 HP3 K1 K2 K3 K4 K5 Ha0 Hgb Hsrc Hfd3 Hfs3.
pose proof HFR as (_ & _ & _ & _ & _ & _ & HJ0 & _).
pose proof (fun a => pm_apart cx fpos ly2 S2 W2 (ms_mem ms) md _ a HPRE HJ0) as HAP. clear HJ0.
destruct cx as [STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k regs ch ps n b M C cid pos].
unfold op_gi_read, op_mid, op_fopen_ret, oSH, oFL, oF, op_pre, osp1, OP_HDR, OP_FLAGPTR in *.
cbn [o_STK o_sp0 o_FP o_ly o_S o_W0 o_mem0 o_md0 o_own o_lyc o_Sc o_W o_memc o_mdc o_k
  o_regs o_ch o_ps o_n o_b o_M o_C o_cid o_pos] in *.
pm_unpack_fr HFR.
destruct HPRE as (HJc & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & _ & _ & Hown & Hfa1 & Hfa2 & _ & Hps8 &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & HnC & _).
destruct (Hn1 Hn1') as (Hh4096 & Hh16 & Hab & Hunb & Hmo & HFP). clear Hn0 Hn1.
pose proof HJc as (HAR & _ & _ & _ & _ & Hfrsc & _).
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
pose proof HJc' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresc & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
destruct (pm_ly_F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [EFA2 _].
destruct (pm_ly_F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as [EFAc _].
assert (EFA : forall c q, frame_addr ly2 c q = frame_addr lyc c q) by (intros c q; rewrite EFA2, EFAc; reflexivity).
clear EFA2 EFAc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TPCAP_SOURCE_OPEN_STK = 18736) by reflexivity.
unfold OP_CID in *.
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrsc; apply in_or_app; left; exact Hown).
assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; right; exact Hin).
assert (HinF : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hc4096 & Hcceil & Hcapp).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 (ms_mem ms) md 1 fpos HAR2 HinF) as (HF4096 & HFceil & HFapp).
pose proof (frame_al64 SEGS B ly2 S2 W2 (ms_mem ms) md 1 fpos HAR2 HinF) as (HFa64 & _ & _).
rewrite EFA in HF4096, HFceil, HFapp, HFa64.
destruct (in_split _ _ Hin) as (l2 & l3 & El).
pose proof (sep_frames_pos SEGS B LAWS ly2 S2 W2 (ms_mem ms) md (1, fpos) (cid, pos) [] l2 l3 HAR2
  ltac:(rewrite Hfrs2, El; reflexivity)) as DFc.
unfold zdisjoint, frame_rng in DFc. cbn [fst snd] in DFc. rewrite !EFA in DFc.
assert (Hfin : In (h, SRC_FILE_BLOCK) (ablocks B ly2 S2)) by (rewrite Hab; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly2 S2 W2 (ms_mem ms) md h SRC_FILE_BLOCK HAR2 Hfin) as (_ & _ & Hhceil & Hhia & _).
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 (ms_mem ms) md h SRC_FILE_BLOCK 1 fpos HAR2 Hfin HinF) as DhF.
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 (ms_mem ms) md h SRC_FILE_BLOCK cid pos HAR2 Hfin Hin2) as DhP.
unfold zdisjoint in DhF, DhP. cbn [fst snd] in DhF, DhP. rewrite EFA in DhF, DhP.
assert (Hnotf : ~ In (h, SRC_FILE_BLOCK) (ablocks B lyc Sc))
  by (apply (pm_last_notin ly2 S2 W2 (ms_mem ms) md _ _ HAR2 Hab); cbn [snd]; change (req_size SRC_FILE_BLOCK) with 1304; lia).
change (req_size SRC_FILE_BLOCK) with 1304 in *.
set (F := frame_addr lyc 1 fpos) in *.
change (fs_frame_bytes 1) with 128 in *.
set (sp1 := 32 * ((spZ regs - OPEN_FRAME) / 32)) in *.
assert (Hsp64 : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply u64_range).
destruct (pm_osp1_facts (spZ regs) ltac:(lia) Hal16) as (Hsp1r & Hsp1al).
change OPEN_FRAME with 96 in sp1. fold sp1 in Hsp1r, Hsp1al.
assert (Hsp_lo : alloc_ceiling + 18736 <= spZ regs) by lia.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hcapp, HFapp, Hhia.
destruct (pm_div8 F HFa64) as [EF8 EF64].
assert (HF8b : 0 <= F / 8 /\ F / 8 + 16 <= 2 ^ 44) by (rewrite EF8; lia).
assert (HIE : pcap_img_end = (symaddr ImgPages.AsanUbsan.top)) by reflexivity.
(* The separations the goals below need, each from the one disjunction it uses; then the disjunctions go. *)
assert (O_hi : forall a, sp1 <= a < 2 ^ 64 -> ~ ((ps <= a < ps + 8) \/ (ps + 12 <= a < ps + 22) \/
  (SHADOW_OFF + F / 8 + 4 <= a < SHADOW_OFF + F / 8 + 7)))
  by (intros a Ha; clear - Ha Hsp1r Hsp_lo Hcceil Hfa2 HF8b C1; unfold SHADOW_OFF; lia).
assert (O_F : forall a, F <= a < F + 128 -> ~ ((ps <= a < ps + 8) \/ (ps + 12 <= a < ps + 22) \/
  (SHADOW_OFF + F / 8 + 4 <= a < SHADOW_OFF + F / 8 + 7)))
  by (intros a Ha; clear - Ha DFc Hfa1 Hfa2 HFapp HF8b; unfold SHADOW_OFF; lia).
assert (O_P8 : forall a, ps + 8 <= a < ps + 12 -> ~ ((ps <= a < ps + 8) \/ (ps + 12 <= a < ps + 22) \/
  (SHADOW_OFF + F / 8 + 4 <= a < SHADOW_OFF + F / 8 + 7)))
  by (intros a Ha; clear - Ha Hcapp Hfa1 Hfa2 HF8b; unfold SHADOW_OFF; lia).
assert (O_img : forall a, in_img SEGS a -> ~ ((ps <= a < ps + 8) \/ (ps + 12 <= a < ps + 22) \/
  (SHADOW_OFF + F / 8 + 4 <= a < SHADOW_OFF + F / 8 + 7))).
{ intros a Hi. pose proof (pa_img_range a Hi) as Hr1. intros [Hp|[Hp|Hp]].
  - exact (frm_img SEGS B LAWS lyc Sc W memc mdc cid pos a HAR Hin ltac:(clear - Hp Hfa1 Hfa2; lia) Hi).
  - exact (frm_img SEGS B LAWS lyc Sc W memc mdc cid pos a HAR Hin ltac:(clear - Hp Hfa1 Hfa2; lia) Hi).
  - clear - Hp Hr1 HIE HF8b. unfold SHADOW_OFF in Hp. lia. }
assert (O_SH : forall i, 0 <= i < 16 -> ~ (4 <= i < 7) -> ~ ((ps <= SHADOW_OFF + F / 8 + i < ps + 8) \/
  (ps + 12 <= SHADOW_OFF + F / 8 + i < ps + 22) \/
  (SHADOW_OFF + F / 8 + 4 <= SHADOW_OFF + F / 8 + i < SHADOW_OFF + F / 8 + 7)))
  by (intros i Hi Hn; clear - Hi Hn Hcapp Hfa1 Hfa2 HF8b; unfold SHADOW_OFF; lia).
assert (NW_hi : forall a, sp1 <= a -> ~ rread_wrset h (F + 32) 24 a)
  by (intros a Ha; clear - Ha Hhceil HFceil Hsp1r Hsp_lo; unfold rread_wrset, SRC_FILE_BLOCK; lia).
assert (NW_F : forall a, F <= a < F + 128 -> ~ (F + 32 <= a < F + 56) -> ~ rread_wrset h (F + 32) 24 a)
  by (intros a Ha Hn; clear - Ha Hn DhF; unfold rread_wrset, SRC_FILE_BLOCK; lia).
assert (NW_SH : forall i, 0 <= i < 16 -> ~ rread_wrset h (F + 32) 24 (SHADOW_OFF + F / 8 + i))
  by (intros i Hi; clear - Hi Hhia HFapp HF8b; unfold rread_wrset, SRC_FILE_BLOCK, SHADOW_OFF; lia).
assert (NW_PS : forall a, ps <= a < ps + 24 -> ~ rread_wrset h (F + 32) 24 a)
  by (intros a Ha; clear - Ha DhP DFc Hfa1 Hfa2; unfold rread_wrset, SRC_FILE_BLOCK; lia).
clear Hcapp HFapp Hhia DFc DhF DhP.
assert (Esp : spZ (ms_regs mc) = sp1)
  by (unfold spZ; rewrite (QK 2%bv) by (cbn; tauto); rewrite R2; apply unsigned_lit_small; lia).
rewrite Esp in K1, K5. unfold AFREAD_STK in K1, K5.
assert (UN3 : forall a, sp1 <= a < 2 ^ 64 -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) (ms_mem ms) a).
{ intros a Ha. rewrite K1; [| lia | lia | exact (NW_hi a ltac:(lia))].
  apply UNc; [lia | exact (O_hi a Ha)]. }
assert (UNF : forall a, F <= a < F + 128 -> ~ (F + 32 <= a < F + 56) ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) (ms_mem ms) a).
{ intros a Ha Hn. rewrite (K4 1 fpos a HinF).
  - apply UNc; [lia | exact (O_F a Ha)].
  - left. unfold frame_rng, in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 1) with 128. fold F. lia.
  - exact (NW_F a Ha Hn). }
assert (USH : forall i, 0 <= i < 16 -> aview SEGS (w_H W3) mem3 (SHADOW_OFF + F / 8 + i) =
  aview SEGS (w_H W2) (ms_mem mc) (SHADOW_OFF + F / 8 + i)).
{ intros i Hi. apply (K4 1 fpos _ HinF).
  - right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 1 / 8) with 16. fold F. lia.
  - exact (NW_SH i Hi). }
assert (UPS : forall a, ps <= a < ps + 24 -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) (ms_mem mc) a).
{ intros a Ha. apply (K4 cid pos a Hin2).
  - left. unfold frame_rng, in_zr. cbn [fst snd]. rewrite EFA. lia.
  - exact (NW_PS a Ha). }
assert (Hj : rread_k 24 (Z.of_nat (length C)) 0 = Z.min 24 n) by (unfold rread_k; rewrite Z.sub_0_r, <- HnC; reflexivity).
rewrite Hj in Ha0, Hgb, Hsrc.
exists h, (Z.min 24 n).
split; [cbn [ms_pc_val mkst]; rewrite Q1; reflexivity|].
split.
2: { split; [exact Hn1'|]. split; [exact Hh4096|]. split; [exact Hh16|]. split; [exact Hab|].
     split; [exact Ha0|]. split; [reflexivity|].
     split; [exact Hgb|]. split; [rewrite Z.add_0_l in Hsrc; exact Hsrc|]. split; [exact HFP | exact Hmo]. }
cbn [ms_regs ms_mem ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact HJ3|].
split; [lia|].
split; [unfold EV_FUZZ_FOPEN in Hnev2; exact Hnev2|].
split; [exact Hfrs2|]. split; [exact Hnin2|]. split; [exact HfsS2|].
split; [pm_regq HP3 QK 2 (2%bv : bv 5) R2|].
split; [pm_regq HP3 QK 8 (8%bv : bv 5) R8|].
split; [pm_regq HP3 QK 9 (9%bv : bv 5) R9|].
split; [pm_regq HP3 QK 18 (18%bv : bv 5) R18|].
split; [pm_regq HP3 QK 19 (19%bv : bv 5) R19|].
split; [etransitivity; [exact (HP3 20 ltac:(unfold acallee_saved; lia))|]; exact Q20|].
split; [pm_regq HP3 QK 21 (21%bv : bv 5) R21|].
split; [pm_regq HP3 QK 22 (22%bv : bv 5) R22|].
split; [etransitivity; [exact (HP3 23 ltac:(unfold acallee_saved; lia))|]; exact Q23|].
split; [etransitivity; [exact (HP3 24 ltac:(unfold acallee_saved; lia))|]; exact Q24|].
split; [etransitivity; [exact (HP3 25 ltac:(unfold acallee_saved; lia))|]; exact Q25|].
split; [pm_regq HP3 QK 3 (3%bv : bv 5) R3|].
split; [pm_regq HP3 QK 4 (4%bv : bv 5) R4|].
split; [pm_regq HP3 QK 26 (26%bv : bv 5) R26|].
split; [pm_regq HP3 QK 27 (27%bv : bv 5) R27|].
split; [rewrite (pm_rdword_agree (aview SEGS (w_H W2) (ms_mem ms))); [exact Hra | intros i Hi; apply UN3; lia]|].
split; [intros j Hj'; rewrite (pm_rdword_agree (aview SEGS (w_H W2) (ms_mem ms)));
        [exact (Hsav j Hj') | intros i Hi; apply UN3; lia]|].
split; [rewrite (pm_rdword_agree (aview SEGS (w_H W2) (ms_mem ms))); [exact HMG | intros i Hi; apply UNF; lia]|].
split; [rewrite (pm_rdword_agree (aview SEGS (w_H W2) (ms_mem ms))); [exact HO8 | intros i Hi; apply UNF; lia]|].
split; [rewrite (pm_rdword_agree (aview SEGS (w_H W2) (ms_mem ms))); [exact HO16 | intros i Hi; apply UNF; lia]|].
split; [rewrite (pm_rdword_agree (aview SEGS (w_H W2) (ms_mem ms))); [exact HFLP | intros i Hi; apply UNF; lia]|].
split; [reflexivity|].
split.
{ intros i Hi. rewrite (USH (Z.of_nat i)) by lia.
  destruct (Nat.lt_ge_cases i 4) as [Hc|Hc]; [|destruct (Nat.lt_ge_cases i 7) as [Hc2|Hc2]].
  - rewrite UNc; [| unfold SHADOW_OFF; lia | apply O_SH; lia]. rewrite (Hsh i Hi).
    do 4 (destruct i as [|i]; [reflexivity|]). lia.
  - rewrite (SHc (Z.of_nat i)) by lia. do 7 (destruct i as [|i]; [first [lia | reflexivity]|]). lia.
  - rewrite UNc; [| unfold SHADOW_OFF; lia | apply O_SH; lia]. rewrite (Hsh i Hi).
    do 16 (destruct i as [|i]; [first [lia | reflexivity]|]). lia. }
split; [eapply pm_vm_frame; [|exact V0]; intros x Hx; apply (mbyte_of_aview SEGS); apply UPS; cbn in Hx; lia|].
split; [eapply pm_vm_frame; [|exact V12]; intros x Hx; apply (mbyte_of_aview SEGS); apply UPS; cbn in Hx; lia|].
split; [eapply pm_vm_frame; [|exact V16]; intros x Hx; apply (mbyte_of_aview SEGS); apply UPS; cbn in Hx; lia|].
split; [eapply pm_vm_frame; [|exact V20]; intros x Hx; apply (mbyte_of_aview SEGS); apply UPS; cbn in Hx; lia|].
split; [intros i Hi; rewrite UPS by lia; rewrite UNc; [exact (HPS0 i ltac:(lia)) | lia | exact (O_P8 (ps + i) ltac:(lia))]|].
split.
{ assert (HK0 : topen_kept SK SEGS B lyc Sc W memc W2 (ms_mem ms) (spZ regs - TPCAP_SOURCE_OPEN_STK) (spZ regs)
                  (fun a => ps <= a < ps + 22)) by (apply pm_topen_kept_weak; exact HKEPT).
  assert (HK1 : topen_kept SK SEGS B lyc Sc W memc W2 (ms_mem mc) (spZ regs - TPCAP_SOURCE_OPEN_STK) (spZ regs)
                  (fun a => ps <= a < ps + 22)).
  { apply (pm_topen_kept_upd lyc Sc W memc mdc W2 (ms_mem ms) (ms_mem mc) _ _ _
      (fun a => (ps <= a < ps + 8) \/ (ps + 12 <= a < ps + 22) \/ (SHADOW_OFF + F / 8 + 4 <= a < SHADOW_OFF + F / 8 + 7))
      HAR HK0).
    - intros a Ha Hn. exact (UNc a Ha Hn).
    - intros a HZa. cbv beta in HZa. destruct HZa as [HZa | [HZa | HZa]].
      + split; [lia|]. split; [exact (frm_img SEGS B LAWS lyc Sc W memc mdc cid pos a HAR Hin ltac:(clear - HZa Hfa1 Hfa2; lia))|].
        split; [intros b0 m0 _ _; cbv beta; lia | intros c q _ _; cbv beta; lia].
      + split; [lia|]. split; [exact (frm_img SEGS B LAWS lyc Sc W memc mdc cid pos a HAR Hin ltac:(clear - HZa Hfa1 Hfa2; lia))|].
        split; [intros b0 m0 _ _; cbv beta; lia | intros c q _ _; cbv beta; lia].
      + destruct (HAP a ltac:(right; lia)) as (Ha1 & Hi & Hb & Hf).
        split; [lia|]. split; [exact Hi|]. split.
        * intros b0 m0 Hb0 Hr. exfalso. apply (Hb b0 m0); [rewrite Hab; apply in_or_app; left; exact Hb0 | exact Hr].
        * intros c q Hcq Hr. exfalso. destruct (Hf c q Hcq) as [Hf1 Hf2]. destruct Hr; contradiction.
    - intros a Ha. apply Hpresc. lia. }
  apply (pm_topen_kept_rk lyc Sc W memc ly2 S2 W2 (ms_mem mc) W3 mem3 _ _ (sp1 - 8192) sp1 _
    (rread_wrset h (F + 32) 24) HK1 K1 K2 K3 K4 K5).
  - lia.
  - lia.
  - intros a Ha. unfold rread_wrset, SRC_FILE_BLOCK in Ha. lia.
  - intros b0 m0 Hb. rewrite Hab. apply in_or_app. left. exact Hb.
  - intros b0 m0 i Hb Hi Hw. unfold rread_wrset, SRC_FILE_BLOCK in Hw.
    assert (Hb2 : In (b0, m0) (ablocks B ly2 S2)) by (rewrite Hab; apply in_or_app; left; exact Hb).
    assert (Hne : (b0, m0) <> (h, SRC_FILE_BLOCK)) by (intros Heq; rewrite Heq in Hb; exact (Hnotf Hb)).
    pose proof (sep_blocks SEGS B LAWS ly2 S2 W2 (ms_mem ms) md b0 m0 h SRC_FILE_BLOCK HAR2 Hb2 Hfin Hne) as D.
    pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 (ms_mem ms) md b0 m0 1 fpos HAR2 Hb2 HinF) as D2.
    unfold zdisjoint in D, D2. cbn [fst snd] in D, D2. rewrite EFA in D2. change (req_size SRC_FILE_BLOCK) with 1304 in D.
    change (fs_frame_bytes 1) with 128 in D2. fold F in D2. lia.
  - intros c q Hcq. rewrite Hfrs2. right. exact Hcq.
  - exact EFA.
  - intros c q a Hcq Hr Hw. unfold rread_wrset, SRC_FILE_BLOCK in Hw.
    destruct Hw as [Hw | Hw].
    + assert (Hcq2 : In (c, q) (frames S2)) by (rewrite Hfrs2; right; exact Hcq).
      pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 (ms_mem ms) md h SRC_FILE_BLOCK c q HAR2 Hfin Hcq2) as D.
      unfold zdisjoint in D. cbn [fst snd] in D. rewrite EFA in D. change (req_size SRC_FILE_BLOCK) with 1304 in D.
      destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc c q HAR Hcq) as (Hg4096 & Hgceil & _).
      destruct (al_blocks _ _ LAWS ly2 S2 W2 (ms_mem ms) md h SRC_FILE_BLOCK HAR2 Hfin) as (_ & _ & _ & Hhia' & _).
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hhia'. change (req_size SRC_FILE_BLOCK) with 1304 in Hhia'.
      pose proof (fs_frame_bytes_nonneg c) as Hnn.
      pose proof (shadow_addr_bounds (frame_addr lyc c q) ltac:(lia)) as Hsb1.
      pose proof (shadow_addr_bounds (frame_addr lyc c q + fs_frame_bytes c) ltac:(lia)) as Hsb2.
      pose proof (shadow_range_end (frame_addr lyc c q) (fs_frame_bytes c) Hnn) as Hse.
      unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. destruct Hr; lia.
    + destruct (HAP a ltac:(left; lia)) as (_ & _ & _ & Hf). destruct (Hf c q Hcq) as [Hf1 Hf2]. destruct Hr; contradiction.
  - intros a Ha. apply Hpres3. lia. }
split; [rewrite Hfd3, Hfdc; exact Hfds|]. split; [rewrite Hfs3, Hfsc; exact Hfs|].
split; [eapply pm_meta_between; [exact HJ | exact HJ3 | exact HMETA]|].
split.
{ apply (pm_rodata_frame (aview SEGS (w_H W2) (ms_mem ms))); [|exact HROD].
  intros a Hi Ho He. pose proof (pa_img_range a Hi) as Hr1. rewrite (K3 a Hi Ho He).
  apply UNc; [lia | exact (O_img a Hi)]. }
eapply achain_kept with (lo := sp1); [exact Hch | lia | lia | intros a Ha; apply UN3; lia].
Qed.

(* The token runs extend the environment above its 512 register and image atoms (YCbn.v:21-24 extK). *)
Lemma pm_ewset_agree : forall k E n w, (k <= n)%nat -> env_agree k E (ewset E n w).
Proof. intros k E n w Hk. split; [intros i Hi; apply ew_ewset_other; lia | reflexivity]. Qed.
Lemma pm_agree_weak : forall k k' E E', (k <= k')%nat -> env_agree k' E E' -> env_agree k E E'.
Proof. intros k k' E E' Hk [H1 H2]. split; [intros n Hn; apply H1; lia | exact H2]. Qed.
Ltac pm_agree :=
  lazymatch goal with
  | |- env_agree ?k ?E ?E => apply env_agree_refl
  | |- env_agree ?k ?E (ewset ?X ?n ?w) =>
      apply (env_agree_trans k E X (ewset X n w)); [pm_agree | apply pm_ewset_agree; lia]
  end.
(* The facts of the walk's register atoms, carried to the run's new environment. *)
Ltac pm_lift AG E10 E19 U19 E21 U21 E22 E32 HAE :=
  let O := fresh "O" in pose proof (proj1 AG) as O;
  rewrite <- (O 10%nat ltac:(lia)) in E10; rewrite <- (O 19%nat ltac:(lia)) in E19, U19;
  rewrite <- (O 21%nat ltac:(lia)) in E21, U21; rewrite <- (O 22%nat ltac:(lia)) in E22;
  rewrite <- (O 32%nat ltac:(lia)) in E32;
  let H := fresh "HAEn" in
  pose proof (env_agree_trans 32 _ _ _ HAE (pm_agree_weak 32 512 _ _ ltac:(lia) AG)) as H;
  clear HAE O AG; rename H into HAE.
Ltac pm_newenv HS Eold Enew E10 E19 U19 E21 U21 E22 E32 HAE :=
  let AG := fresh "AG" in
  let Ex := lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => Ex | st_ok _ ?Ex _ _ => Ex end in
  first
  [ constr_eq Ex Eold; set (Enew := Eold) in *
  | assert (AG : env_agree 512 Eold Ex) by pm_agree; set (Enew := Ex) in *;
    pm_lift AG E10 E19 U19 E21 U21 E22 E32 HAE ].

(* What a run kept: every byte outside its regions' windows (YC4b.v:230 kept_of_frame). *)
Ltac pm_kept HFr Zs U19 U21 UN :=
  lazymatch type of HFr with frame_of ?Ex ?rsP (mrestrict ?Hh (ms_mem ?m0)) (mrestrict _ (ms_mem ?m1)) =>
    pose proof (kept_of_frame (segs := SEGS) Ex rsP Hh (ms_mem m0) (ms_mem m1) Zs HFr
      ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
            repeat (destruct HinW as [HqW | HinW];
                    [injection HqW as <- <- <-; cbn [base_val] in HrrW; rewrite ?U19, ?U21 in HrrW; lia|]);
            destruct HinW)) as UN end.

(* ---- the walk --------------------------------------------------------------------------------------------- *)
Theorem op_from_fopen :
  op_from SK B K MT FM_RA CTX roimg (op_gi_null SK B K MT) ->
  op_from SK B K MT FM_RA CTX roimg (op_gi_read SK B K MT) ->
  op_from_fopen_stmt SK B K MT FM_RA CTX roimg.
Proof.
intros OFN OFR. unfold op_from_fopen_stmt. intros cx fpos h ly2 S2 W2 ms md HPRE HFR.
destruct (pm_entry cx fpos h ly2 S2 W2 ms md HPRE HFR) as [HS SHOK].
pose proof HPRE as HPRE0. pose proof HFR as HFR0.
destruct cx as [STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k regs ch ps n b M C cid pos].
unfold op_fopen_ret, oSH, oFL, oF, osp1 in HFR. unfold op_pre in HPRE.
cbn [o_STK o_sp0 o_FP o_ly o_S o_W0 o_mem0 o_md0 o_own o_lyc o_Sc o_W o_memc o_mdc o_k
  o_regs o_ch o_ps o_n o_b o_M o_C o_cid o_pos] in HFR, HPRE.
pm_unpack_fr HFR.
destruct HPRE as (HJc & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & _ & _ & Hown & Hfa1 & Hfa2 & _ & Hps8 &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & HnC & _).
pose proof HJc as (HAR & _ & _ & _ & _ & Hfrsc & _).
pose proof HJ as (HAR2 & _).
destruct (pm_ly_F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [EFA2 _].
destruct (pm_ly_F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as [EFAc _].
assert (EFA : forall c q, frame_addr ly2 c q = frame_addr lyc c q) by (intros c q; rewrite EFA2, EFAc; reflexivity).
clear EFA2 EFAc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold OP_CID in *.
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrsc; apply in_or_app; left; exact Hown).
assert (HinF : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hc4096 & Hcceil & Hcapp).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 (ms_mem ms) md 1 fpos HAR2 HinF) as (HF4096 & HFceil & HFapp).
pose proof (frame_al64 SEGS B ly2 S2 W2 (ms_mem ms) md 1 fpos HAR2 HinF) as (HFa64 & _ & _).
rewrite EFA in HF4096, HFceil, HFapp, HFa64.
destruct (in_split _ _ Hin) as (l2 & l3 & El).
pose proof (sep_frames_pos SEGS B LAWS ly2 S2 W2 (ms_mem ms) md (1, fpos) (cid, pos) [] l2 l3 HAR2
  ltac:(rewrite Hfrs2, El; reflexivity)) as DFc.
unfold zdisjoint, frame_rng in DFc. cbn [fst snd] in DFc. rewrite !EFA in DFc.
set (F := frame_addr lyc 1 fpos) in *.
change (fs_frame_bytes 1) with 128 in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hcapp, HFapp.
destruct (pm_div8 F HFa64) as [EF8 EF64].
assert (HF8b : 0 <= F / 8 /\ F / 8 + 16 <= 2 ^ 44) by (rewrite EF8; lia).
assert (Hh64 : 0 <= h < 2 ^ 64).
{ destruct (Z.eq_dec n 0) as [Hz|Hz].
  - destruct (Hn0 Hz) as (-> & _). lia.
  - destruct (Hn1 ltac:(lia)) as (Hh4096 & _ & Hab & _).
    assert (Hfin : In (h, SRC_FILE_BLOCK) (ablocks B ly2 S2)) by (rewrite Hab; apply in_or_app; right; left; reflexivity).
    destruct (al_blocks _ _ LAWS ly2 S2 W2 (ms_mem ms) md h SRC_FILE_BLOCK HAR2 Hfin) as (_ & _ & Hhc & _).
    change (req_size SRC_FILE_BLOCK) with 1304 in Hhc. lia. }
remember (Eimg (Ereg (ms_regs ms) pm_extra)) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall nn, (nn < A_TEXT)%nat -> ew E nn = ew (Ereg (ms_regs ms) pm_extra) nn)
  by (intros nn Hn; subst E; apply Eimg_low; exact Hn).
assert (ER : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> (nn < 32)%nat -> ew E nn = getr (ms_regs ms) r)
  by (intros nn r Hr Hn; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hr).
assert (HAE : env_agree 32 (Ereg (ms_regs ms) pm_extra) E)
  by (split; [intros nn Hn'; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (E10 : ew E 10 = w64 h) by (rewrite (ER 10%nat 10%bv eq_refl) by lia; exact R10).
assert (E19 : ew E 19 = w64 ps) by (rewrite (ER 19%nat 19%bv eq_refl) by lia; exact R19).
assert (E21 : ew E 21 = w64 (SHADOW_OFF + F / 8)) by (rewrite (ER 21%nat 21%bv eq_refl) by lia; exact R21).
assert (E22 : ew E 22 = w64 F) by (rewrite (ER 22%nat 22%bv eq_refl) by lia; exact R22).
assert (E32 : ew E 32 = w64 pm_SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms) pm_extra 0)).
assert (U19 : bv_unsigned (ew E 19) = ps) by (rewrite E19; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = SHADOW_OFF + F / 8) by (rewrite E21; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
clear HEdef EL ER.
(* 0x812f8 .. 0x81364: the two UBSan guards on ps, the four shadow tests and stores into ps, up to the test of f.
   G5a, 0x812f8 `beqz s3` to the `unimp` at 0x8153c: decided NOT taken by this run, decide_cond2 (Reusable/YP0e.v:932)
   on BC_EQ with decide_eq's range test (Reusable/YP0m.v:658-672, the SOff / SLit
   arm :665-666) on atom 19 (s3 = ps) against 0 from its fact
   HPTR 3, lo 4096 (pm_facts; pm_entry proves it from op_pre's frame of ps, frames_bounds). G5b, 0x81300
   `andi a0,s3,7` / 0x81304 `bnez a0` to 0x8153c: s_and_ptr (Reusable/YP0m.v:969-980) gives 0 from the same
   fact's alignment 2^3 (op_pre's ps mod 8 = 0), so the branch is NOT taken. Templates: the released UBSan proof of
   the v1.8 image, lib/U/Prog/pcap_source_open.v at c8557374ad2e, :114 and :115 (premise :93) in open_null and :334
   and :335 (premise :290) in open_mid; the earlier walk of this image, on a working branch
   a8ccd33b1a7, pcap_source_open_fo.v (sha256 b7425f5b4c84; internal record) :66 / :68 and :132 / :134.
   The shadow tests 0x81310 `lbu` / 0x81314 `bnez` (report_store8 at 0x81598), 0x81328 `lb` / 0x8132c `bnez` (slow
   block 0x81540), 0x81340 / 0x81344 (0x81550) and 0x81358 / 0x8135c (0x81560) read the shadow of ps, ps + 12,
   ps + 16 and ps + 20 through ps's shadow entry pm_SH (pm_shent_ok, from op_fopen_ret's range_addressable of ps's
   24 bytes; ps is 8-aligned, so every byte read is 0): the token run decides each `bnez` NOT taken, and no slow block
   or report call is ever reached. Templates: pcap_source_open_fo.v (sha256 b7425f5b4c84; internal record) :71, :76, :80, :84 and :137, :142, :146, :150. *)
paj_run_tok (paj_run (SK := SK) (PI := PI) B LAWS) HS HJ SHOK pm_span;
  [ pm_awr cid pos fpos Hown EFA U19 U21 F | ].
pm_kept HFr (fun a => (ps <= a < ps + 8) \/ (ps + 12 <= a < ps + 22)) U19 U21 UN1.
clear HF HFr HG.
pm_newenv HS E E1 E10 E19 U19 E21 U21 E22 E32 HAE.
(* 0x81364 `beqz a3`: f = NULL goes to the cut 0x813f8 *)
psrr_branch_tok (paj_run (SK := SK) (PI := PI) B LAWS) (paj_branch (PI := PI)) HS SHOK pm_span.
- rewrite branch_eq_U, (U_atom _ 10 h E10 Hh64), U_lit in Hc by lia. apply Z.eqb_eq in Hc. subst h.
  assert (Hnz : n = 0) by (destruct (Z.eq_dec n 0) as [Hz|Hz]; [exact Hz | destruct (Hn1 ltac:(lia)) as (H4 & _); lia]).
  paj_run_to_tok (paj_run_to (SK := SK) (PI := PI) B LAWS) HS HJ SHOK pm_span OP_CUT_NULL;
    [ pm_awr cid pos fpos Hown EFA U19 U21 F | ].
  pm_kept HFr (fun a => (ps <= a < ps + 8) \/ (ps + 12 <= a < ps + 22)) U19 U21 UN2.
  clear HF HFr HG.
  pm_newenv HS E1 E2 E10 E19 U19 E21 U21 E22 E32 HAE.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?m3) =>
    pose proof HS as (Hf3 & Hpc3 & Hsv3 & Hrv3 & Hfc3 & Hrom3 & _);
    cbn [restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom abs_ss setpc ss_pc ss_resv resv_denot]
      in Hf3, Hpc3, Hsv3, Hrv3, Hfc3, Hrom3;
    pose proof (regs_kept_of_st_ok_pi _ _ _ (ms_regs ms) pm_extra pm_keepN HS HAE ltac:(vm_compute; reflexivity)) as REG;
    cbn [ms_regs restrict] in REG;
    let rA := eval vm_compute in (nth 0 (ss_mem ssx) r_pmA) in
    let rB := eval vm_compute in (nth 1 (ss_mem ssx) r_pmA) in
    pose proof (st_ok_pi_region_nth _ ssx (restrict (w_H W2) m3) 0 rA HS ltac:(vm_compute; reflexivity)) as HRgA;
    pose proof (st_ok_pi_region_nth _ ssx (restrict (w_H W2) m3) 1 rB HS ltac:(vm_compute; reflexivity)) as HRgB;
    cbn [restrict ms_mem] in HRgA, HRgB end.
  pm_prreg_raw HS (23%bv : bv 5) Q23. pm_prreg_raw HS (24%bv : bv 5) Q24.
  rewrite (denot_shx _ 19 32 0 ps pm_SB E19 E32) in Q24 by (unfold pm_SB; lia).
  lazymatch goal with |- SRr _ _ (mkCfg ?m3 ?d3) _ =>
    assert (Q23' : getr (ms_regs m3) 23%bv = w64 SHADOW_OFF)
      by (rewrite Q23; cbn [sv_denot]; rewrite E32; reflexivity);
    assert (Q24' : getr (ms_regs m3) 24%bv = w64 (SHADOW_OFF + ps / 8))
      by (rewrite Q24; unfold w64, pm_SB, SHADOW_OFF; rewrite Z.add_0_r; reflexivity);
    assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ ((ps <= a < ps + 8) \/ (ps + 12 <= a < ps + 22)) ->
              aview SEGS (w_H W2) (ms_mem m3) a = aview SEGS (w_H W2) (ms_mem ms) a)
      by (intros a Ha Hna; rewrite (UN2 a Ha Hna); apply (UN1 a Ha Hna));
    pose proof (field_of_region _ _ 19 ps _ _ _ _ _ 0 8%N (SOff 10 0) 0 HRgA U19 ltac:(cbn; tauto)
      ltac:(cbn [sv_denot]; rewrite E10; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as V0;
    pose proof (field_of_region _ _ 19 ps _ _ _ _ _ 12 4%N (SLit 0) 0 HRgB U19 ltac:(cbn; tauto)
      eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V12;
    pose proof (field_of_region _ _ 19 ps _ _ _ _ _ 16 4%N (SLit 0) 0 HRgB U19 ltac:(cbn; tauto)
      eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V16;
    pose proof (field_of_region _ _ 19 ps _ _ _ _ _ 20 2%N (SLit 0) 0 HRgB U19 ltac:(cbn; tauto)
      eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V20;
    rewrite Z.add_0_r in V0; change (N.to_nat 8) with 8%nat in V0; change (N.to_nat 4) with 4%nat in V12, V16;
    change (N.to_nat 2) with 2%nat in V20;
    exact (OFN (mkOCX STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k regs ch ps n b M C cid pos) fpos ly2 S2 W2 m3 d3
      HPRE0 (pm_null_cut (mkOCX STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k regs ch ps n b M C cid pos)
        fpos ly2 S2 W2 ms m3 md d3 HPRE0 HFR0 Hnz Hpc3 Hrv3 Hsv3 Hrom3 Hf3 Hfc3 HJ REG Q23' Q24' UN V0 V12 V16 V20
        ltac:(rewrite !(proj1 (pm_wvb_fds_fs _ _ _)); reflexivity) ltac:(rewrite !(proj2 (pm_wvb_fds_fs _ _ _)); reflexivity)))
  end.
- (* f <> NULL: the buffer in scope, the fread call, its return (0x8138c) *)
  rewrite branch_eq_U, (U_atom _ 10 h E10 Hh64), U_lit in Hc by lia. apply Z.eqb_neq in Hc.
  assert (Hn1' : 1 <= n) by (destruct (Z.eq_dec n 0) as [Hz|Hz]; [exfalso; apply Hc; exact (proj1 (Hn0 Hz)) | lia]).
  paj_run_to_tok (paj_run_to (SK := SK) (PI := PI) B LAWS) HS HJ SHOK pm_span OP_SH_IN;
    [ pm_awr cid pos fpos Hown EFA U19 U21 F | ].
  pm_kept HFr (fun a => (ps <= a < ps + 8) \/ (ps + 12 <= a < ps + 22)) U19 U21 UN2.
  clear HF HFr HG.
  pm_newenv HS E1 E2 E10 E19 U19 E21 U21 E22 E32 HAE.
  (* F's shadow bytes 4 .. 6 (s5, atom 21) as a writable region: 0x8136c..0x81374 store into the shadow band, which
     the token engine refuses (YCbn.v:115-119), so the stretch to the call is walked by the plain run (as
     PcapSourceOpen.v walks 0x8124c..0x812f0). *)
  pose proof HJ as (HAR3 & _).
  destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR3 HinF) as (_ & _ & _ & HFSpres).
  rewrite EFA in HFSpres. change (fs_frame_bytes 1) with 128 in HFSpres. change (128 / 8) with 16 in HFSpres.
  fold F in HFSpres. unfold shadow_addr in HFSpres.
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
    pose proof (st_ok_pi_add_region Ev ssx msx r_pmSH HS eq_refl
      ltac:(unfold region_ok, r_pmSH; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val restrict ms_mem];
            rewrite U21; split; [unfold SHADOW_OFF; lia|]; split; [unfold SHADOW_OFF; lia|]; split; [|constructor];
            intros o Ho; apply (apresent_writable SEGS); exact (proj1 (HFSpres o ltac:(lia))))
      ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
            cbn [all_disjoint]; unfold extent_disjoint, r_pmSH; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
            rewrite U21, U19; unfold SHADOW_OFF; repeat split; lia)) as HS3 end.
  clear HS; rename HS3 into HS; pm_norm_pi HS.
  paj_run_to_sh (SRr_run_to_pi_AJ (SK := SK) B LAWS) HS HJ OP_FREAD_CALL;
    [ pm_awr cid pos fpos Hown EFA U19 U21 F | ].
  pm_kept HFr (fun a => (ps <= a < ps + 8) \/ (ps + 12 <= a < ps + 22) \/
    (SHADOW_OFF + F / 8 + 4 <= a < SHADOW_OFF + F / 8 + 7)) U19 U21 UN3.
  clear HF HFr HG.
  (* ps's shadow entry holds on: the stretch wrote ps and F's shadow bytes 4 .. 6, and ps's shadow is not F's *)
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m2) =>
  lazymatch type of SHOK with sh_ok _ _ _ _ (mrestrict _ (ms_mem ?m1)) =>
    assert (SHOK2 : sh_ok SEGS pm_Bx pm_SH E2 (mrestrict (w_H W2) (ms_mem m2)));
    [ apply (pm_shok_transfer E2 E2 (mrestrict (w_H W2) (ms_mem m1)) _ ps SHOK eq_refl eq_refl);
      [ rewrite (U_atom _ 19 ps E19) by lia; reflexivity
      | unfold pm_Bx; rewrite (U_atom _ 32 pm_SB E32) by (unfold pm_SB; lia); reflexivity
      | intros x Hx; rewrite <- !(aview_rd_of SEGS);
        assert (Hx8 : 0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia);
        destruct (pm_sh_apart F x HFa64 ltac:(lia) ltac:(lia)) as [Hd | Hd];
        apply UN3; unfold SHADOW_OFF in *; lia ]
    | ] end end.
  clear SHOK. rename SHOK2 into SHOK.
  (* 0x81388 `jal`: the call of the fread wrapper's trampoline, by the token run with F's shadow read-only *)
  pm_set_ro HS 0%nat.
  paj_run_tok (paj_run (SK := SK) (PI := PI) B LAWS) HS HJ SHOK pm_span;
    [ pm_awr cid pos fpos Hown EFA U19 U21 F | ].
  pm_kept HFr (fun a => (ps <= a < ps + 8) \/ (ps + 12 <= a < ps + 22)) U19 U21 UN4.
  clear HF HFr HG.
  pm_newenv HS E2 E3 E10 E19 U19 E21 U21 E22 E32 HAE.
  lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?m4) =>
    pose proof (regs_kept_of_st_ok SEGS _ _ _ (ms_regs ms) pm_extra pm_keepR HS HAE ltac:(vm_compute; reflexivity)) as QK;
    cbn [ms_regs restrict] in QK;
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) r_pmA) in
    let r1 := eval vm_compute in (nth 1 (ss_mem ssx) r_pmA) in
    let r2 := eval vm_compute in (nth 2 (ss_mem ssx) r_pmA) in
    pose proof (st_ok_region_nth (segs := SEGS) _ ssx (restrict (w_H W2) m4) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
    pose proof (st_ok_region_nth (segs := SEGS) _ ssx (restrict (w_H W2) m4) 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1;
    pose proof (st_ok_region_nth (segs := SEGS) _ ssx (restrict (w_H W2) m4) 2 r2 HS ltac:(vm_compute; reflexivity)) as HR2;
    cbn [restrict ms_mem] in HR0, HR1, HR2 end.
  pm_prreg_raw HS (1%bv : bv 5) Q1. pm_prreg_raw HS (10%bv : bv 5) Q10. pm_prreg_raw HS (11%bv : bv 5) Q11.
  pm_prreg_raw HS (12%bv : bv 5) Q12. pm_prreg_raw HS (13%bv : bv 5) Q13. pm_prreg_raw HS (20%bv : bv 5) Q20.
  pm_prreg_raw HS (23%bv : bv 5) Q23. pm_prreg_raw HS (24%bv : bv 5) Q24. pm_prreg_raw HS (25%bv : bv 5) Q25.
  rewrite ?wvb_collapse in HJ.
  assert (Q1' : getr (ms_regs ms3) 1%bv = Z_to_bv 64 (BASE + OP_CUT_READ)) by (rewrite Q1; apply codeptr_val; eassumption).
  assert (Q10' : getr (ms_regs ms3) 10%bv = w64 (F + 32)) by (rewrite Q10; apply (pm_denot_off _ 22 F 32 E22); lia).
  assert (Q11' : getr (ms_regs ms3) 11%bv = w64 1) by (rewrite Q11; reflexivity).
  assert (Q12' : getr (ms_regs ms3) 12%bv = w64 24) by (rewrite Q12; reflexivity).
  assert (Q13' : getr (ms_regs ms3) 13%bv = w64 h)
    by (rewrite Q13, (pm_denot_off _ 10 h 0 E10 Hh64), Z.add_0_r; reflexivity).
  assert (Q20' : getr (ms_regs ms3) 20%bv = w64 (F + 32)) by (rewrite Q20; apply (pm_denot_off _ 22 F 32 E22); lia).
  assert (Q23' : getr (ms_regs ms3) 23%bv = w64 SHADOW_OFF) by (rewrite Q23; cbn [sv_denot]; rewrite E32; reflexivity).
  assert (Q24' : getr (ms_regs ms3) 24%bv = w64 (SHADOW_OFF + ps / 8))
    by (rewrite Q24, (denot_shx _ 19 32 0 ps pm_SB E19 E32) by (unfold pm_SB; lia);
        unfold w64, pm_SB, SHADOW_OFF; rewrite Z.add_0_r; reflexivity).
  assert (Q25' : getr (ms_regs ms3) 25%bv = w64 24) by (rewrite Q25; reflexivity).
  clear Q1 Q10 Q11 Q12 Q13 Q20 Q23 Q24 Q25.
  assert (UNc : forall a, 0 <= a < 2 ^ 64 -> ~ ((ps <= a < ps + 8) \/ (ps + 12 <= a < ps + 22) \/
                  (SHADOW_OFF + F / 8 + 4 <= a < SHADOW_OFF + F / 8 + 7)) ->
                aview SEGS (w_H W2) (ms_mem ms3) a = aview SEGS (w_H W2) (ms_mem ms) a)
    by (intros a Ha Hn; rewrite (UN4 a Ha ltac:(cbv beta; tauto)), (UN3 a Ha ltac:(cbv beta; tauto)),
          (UN2 a Ha ltac:(cbv beta; tauto)), (UN1 a Ha ltac:(cbv beta; tauto)); reflexivity).
  pose proof (field_of_region _ _ 21 (SHADOW_OFF + F / 8) _ _ _ _ _ 4 1%N (SLit 0) 0 HR0 U21 ltac:(cbn; tauto)
    eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as VS4.
  pose proof (field_of_region _ _ 21 (SHADOW_OFF + F / 8) _ _ _ _ _ 5 1%N (SLit 0) 0 HR0 U21 ltac:(cbn; tauto)
    eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as VS5.
  pose proof (field_of_region _ _ 21 (SHADOW_OFF + F / 8) _ _ _ _ _ 6 1%N (SLit 0) 0 HR0 U21 ltac:(cbn; tauto)
    eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as VS6.
  change (N.to_nat 1) with 1%nat in VS4, VS5, VS6.
  assert (SHc : forall i, 4 <= i < 7 -> aview SEGS (w_H W2) (ms_mem ms3) (SHADOW_OFF + F / 8 + i) = Some 0).
  { intros i Hi. assert (Hi' : i = 4 \/ i = 5 \/ i = 6) by lia.
    destruct Hi' as [-> | [-> | ->]]; apply pm_aview0; assumption. }
  pose proof (field_of_region _ _ 19 ps _ _ _ _ _ 0 8%N (SOff 10 0) h HR1 U19 ltac:(cbn; tauto)
    ltac:(rewrite (pm_denot_off _ 10 h 0 E10 Hh64), Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as V0.
  pose proof (field_of_region _ _ 19 ps _ _ _ _ _ 12 4%N (SLit 0) 0 HR2 U19 ltac:(cbn; tauto)
    eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V12.
  pose proof (field_of_region _ _ 19 ps _ _ _ _ _ 16 4%N (SLit 0) 0 HR2 U19 ltac:(cbn; tauto)
    eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V16.
  pose proof (field_of_region _ _ 19 ps _ _ _ _ _ 20 2%N (SLit 0) 0 HR2 U19 ltac:(cbn; tauto)
    eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V20.
  rewrite Z.add_0_r in V0. change (N.to_nat 8) with 8%nat in V0. change (N.to_nat 4) with 4%nat in V12, V16.
  change (N.to_nat 2) with 2%nat in V20.
  lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdq _ =>
    assert (Hfdc : m_fds mdq = m_fds md) by (rewrite !(proj1 (pm_wvb_fds_fs _ _ _)); reflexivity);
    assert (Hfsc : m_fs mdq = m_fs md) by (rewrite !(proj2 (pm_wvb_fds_fs _ _ _)); reflexivity) end.
  pose proof (pm_fread_pre (mkOCX STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k regs ch ps n b M C cid pos)
    fpos h ly2 S2 W2 ms ms3 md _ HPRE0 HFR0 Hn1' HJ Q1' QK Q10' Q11' Q12' Q13' UNc SHc) as HPRE1.
  pmkst HS.
  (* the fread wrapper (lib/A/Stdio/PFreadISpec.v afread_spec, the caller-journal form): fread(F + 32, 1, 24, f) *)
  eapply SRr_bind;
    [ exact (AFREAD STK sp0 FP ly S0 W0 mem0 md0 ((1, fpos) :: own) ly2 S2 W2 (ms_mem ms3) _ (k + EV_FUZZ_FOPEN)
        (ms_regs ms3) ((spZ regs, raZ regs, s0Z regs) :: ch) (F + 32) 24 h b 0 C HPRE1) | ].
  cbv beta. intros W3 c3 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (K1 & K2 & K3 & K4 & K5 & K6) &
    (Ely & ES & Ha0 & Hgb & Hsrc & _ & _ & Hfd4 & Hfs4 & _)).
  subst ly4 S4.
  exact (OFR (mkOCX STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k regs ch ps n b M C cid pos) fpos ly2 S2 W3 _ md4
    HPRE0 (pm_read_cut (mkOCX STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k regs ch ps n b M C cid pos)
      fpos h ly2 S2 W2 ms ms3 md _ W3 regs4 mem4 md4 HPRE0 HFR0 Hn1' HJ Q1' QK Q20' Q23' Q24' Q25' UNc SHc
      V0 V12 V16 V20 Hfdc Hfsc HJ4 HP4 K1 K2 K3 K4 K5 Ha0 Hgb Hsrc Hfd4 Hfs4)).
Qed.

End e.
End d.
End b.

(* SK explicit on every exported name that depends on it (a Theorem Labs lane ruling 21:57Z): the only global sink_head instance in this
   closure is the plain build's (lib/Reusable/YI5b.v), so a caller names this image's head. *)
Arguments op_from_fopen {fx rc} SK {PI}.
Arguments pm_entry {fx rc} SK {PI}.
Arguments pm_null_cut {fx rc} SK {PI}.
Arguments pm_fread_pre {fx rc} SK {PI}.
Arguments pm_read_cut {fx rc} SK {PI}.
Arguments pm_ly_F {rc} SK {PI}.
Arguments pm_src_env_img {rc} SK {PI}.
Arguments pm_apart {rc} SK {PI}.
Arguments pm_topen_kept_upd {rc} SK {PI}.
Arguments pm_topen_kept_weak {rc} SK {PI}.
Arguments pm_topen_kept_rk {rc} SK {PI}.
Arguments pm_meta_between {rc} SK {PI}.
(* GUARD: SK must stay explicit. SK is passed by position; were it implicit again, the positional SK would
   land on the next argument and this file would stop compiling. *)
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (PI : PAImg pcap_listing) =>
  op_from_fopen (fx:=fx) (rc:=rc) SK (PI:=PI)).
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (PI : PAImg pcap_listing) =>
  pm_entry (fx:=fx) (rc:=rc) SK (PI:=PI)).
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (PI : PAImg pcap_listing) =>
  pm_null_cut (fx:=fx) (rc:=rc) SK (PI:=PI)).
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (PI : PAImg pcap_listing) =>
  pm_fread_pre (fx:=fx) (rc:=rc) SK (PI:=PI)).
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (PI : PAImg pcap_listing) =>
  pm_read_cut (fx:=fx) (rc:=rc) SK (PI:=PI)).
Check (fun (rc : YM05.RunCeil) (SK : YI16.sink_head) (PI : PAImg pcap_listing) =>
  pm_ly_F (rc:=rc) SK (PI:=PI)).
Check (fun (rc : YM05.RunCeil) (SK : YI16.sink_head) (PI : PAImg pcap_listing) =>
  pm_src_env_img (rc:=rc) SK (PI:=PI)).
Check (fun (rc : YM05.RunCeil) (SK : YI16.sink_head) (PI : PAImg pcap_listing) =>
  pm_apart (rc:=rc) SK (PI:=PI)).
Check (fun (rc : YM05.RunCeil) (SK : YI16.sink_head) (PI : PAImg pcap_listing) =>
  pm_topen_kept_upd (rc:=rc) SK (PI:=PI)).
Check (fun (rc : YM05.RunCeil) (SK : YI16.sink_head) (PI : PAImg pcap_listing) =>
  pm_topen_kept_weak (rc:=rc) SK (PI:=PI)).
Check (fun (rc : YM05.RunCeil) (SK : YI16.sink_head) (PI : PAImg pcap_listing) =>
  pm_topen_kept_rk (rc:=rc) SK (PI:=PI)).
Check (fun (rc : YM05.RunCeil) (SK : YI16.sink_head) (PI : PAImg pcap_listing) =>
  pm_meta_between (rc:=rc) SK (PI:=PI)).

Print Assumptions op_from_fopen.
