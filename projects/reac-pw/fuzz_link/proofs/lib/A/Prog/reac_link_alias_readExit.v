(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a segment of reac_headamp_tx_next on fuzz_grant.asan (NextEntry), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/NextEntry.v at a working branch af735a950e2 (blob 8725db69d2a; the walk was ported from blob 7788bf8f6e4 at a working branch afd75724b5b, which differs from it only by 4 added and 0 removed lines, the licence header), restated over image B's listing, addresses and walk layer (lib/B/Prog) against GrantBContracts.v; frame 96 with twelve saved registers, UBSan traps T1 and T2, and the .rodata divisor read at 0x85fa4 (IMG_NEXT_DIV3) *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/NextEntry.v, with its module paths and module names changed; 542 of its 591 lines of code are new or changed and 711 lines of the source are left out. *)
(* reac_link_alias_read (fuzz_link.asan 0x8867c, listing offset AF_reac_link_alias_read) on image A, THE EXIT PIECE:
   from the EXIT cut (+0x1fc, `lui a1,0x45e03`) to the `ret` (+0x2c4), the obligation `ar_exit_obl` of
   reac_link_alias_readDefs.v.

   The code (listing (internal path) (internal record, sha256 7c23ed8f465f)):
     +0x1fc..+0x204  the retired magic 0x45e0360e at F (s10)
     +0x208          `beqz s2`: s2 = F >= 4096, the real-stack arm +0x25c is dead
     +0x20c..+0x24c  the frame's 16 shadow bytes (s9 = SH) := 0xf5
     +0x250..+0x254  `ld a1,0x78(s2); sb zero,0(a1)`: the frame's flag := 0, THE INLINE RELEASE
     +0x28c..+0x2c4  sp := s0 - 128; ra, s0..s10 reloaded from [s0 - 96, s0); pop; ret
   One plain run (LinkWalkSide.v paj_flag_plain_x) from the cut to the `ret`: the journal loses the frame. Then
   paj_ret_at and apost_side_gen. The symbolic state at the cut: atom i < 32 is register i, atom 32 the frame's
   flag address, atoms 33..44 the words the prologue saved (ra, s0, s1, s2..s10); the regions are the flag byte
   (atom 32), the frame F (atom 18; register 26 is set to the same atom), its shadow SH (atom 25) and the machine
   frame's twelve save slots (atom 8, the entry sp).
   The Post's facts at the cut (ar_pf) come to the end memory by the bytes the run did not write (g_nl, the two
   buffers) and, for the interface table, by the read set kept from the call (arx_tab_kept).

   Proves no function (kind: segment lemma of reac_link_alias_read's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 PcapImgEnd.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkPi LinkWalkSide LinkWalkZsh LinkWalkShadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_link_alias_read_c nl_talk_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_link_alias_readDefs reac_link_alias_readPost.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AF0m AB1v.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* No global sink_head instance is in scope: every journal below is the Section's SK. *)
Fail Definition sink_head_probe_arx : YI16.sink_head := _.

(* ==========================================================================
   0. Constants, the model's buffer lengths, the symbolic data of the cut
   ========================================================================== *)

Lemma arx_consts : SHADOW_OFF = 0x7fff8000 /\ kLowMemEnd = 0x7fff8000 /\ kHighMemBeg = 0x10007fff8000 /\
  kHighMemEnd = 0x800000000000 /\ YImgTop.IMG_LO = 0x10000 /\ YImgTop.IMG_TOP = 0x654000 /\
  LA_G_NL = 0x5dcac0 /\ NK_SIZE = 271992 /\ NK_N_SENT = 271016 /\ NK_IF_NAME = 271024 /\ NK_IF_INDEX = 271664 /\
  fs_frame_bytes AR_CID = 128 /\ fs_frame_bytes AR_CID / 8 = 16 /\ REAC_LINK_ALIAS_READ_AK = 8592.
Proof. repeat split; reflexivity. Qed.

Ltac arx_c :=
  let C := fresh "C" in
  pose proof arx_consts as C;
  repeat match type of C with ?A /\ ?B => let C1 := fresh "C" in destruct C as [C1 C]; try rewrite C1 in * end;
  try rewrite C in *.

(* the C string the reader leaves in a buffer of cap >= 1 bytes is shorter than cap *)
Lemma arx_kind_len : forall tab nm kc ac reqs K, 1 <= kc ->
  Z.of_nat (length (r_kind (read_lib tab nm kc ac reqs K))) <= kc - 1.
Proof.
  intros tab nm kc ac reqs K Hc. unfold read_lib, read_core.
  destruct nm as [s|]; [|cbn [r_kind length]; lia].
  destruct (Nat.eqb (length s) 0); [cbn [r_kind length]; lia|]. cbv zeta.
  destruct (index_of tab s =? 0); [cbn [r_kind length]; lia|]. cbn [r_kind].
  destruct (kc <? 1); [cbn [length]; lia|]. unfold text_of_attr.
  destruct (a_kind (talk_attrs K)); [apply cut_text_len; exact Hc | cbn [length]; lia].
Qed.

Lemma arx_alias_len : forall tab nm kc ac reqs K, 1 <= ac ->
  Z.of_nat (length (r_alias (read_lib tab nm kc ac reqs K))) <= ac - 1.
Proof.
  intros tab nm kc ac reqs K Hc. unfold read_lib, read_core.
  destruct nm as [s|]; [|cbn [r_alias length]; lia].
  destruct (Nat.eqb (length s) 0); [cbn [r_alias length]; lia|]. cbv zeta.
  destruct (index_of tab s =? 0); [cbn [r_alias length]; lia|]. cbn [r_alias].
  destruct (ac <? 1); [cbn [length]; lia|]. unfold text_of_attr.
  destruct (a_alias (talk_attrs K)); [apply cut_text_len; exact Hc | cbn [length]; lia].
Qed.

(* the regions of the cut: the flag byte (atom 32), the frame F (atom 18, its flag word at 120, the magic written
   at 0..8), its sixteen shadow bytes (atom 25), and the twelve save slots below the entry sp (atom 8) *)
Definition arx_flag_r : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 1 [].
Definition arx_frame_r : YP09.region :=
  YP09.mkRegion (Some 18%nat) 0 128 0 8 [YP09.mkChunk 120 (CVal 8 (SOff 32 0))].
Definition arx_shadow_r : YP09.region := YP09.mkRegion (Some 25%nat) 0 16 0 16 [].
Definition arx_save_cs : list YP09.chunk :=
  [ YP09.mkChunk (-96) (CVal 8 (SOff 44 0)); YP09.mkChunk (-88) (CVal 8 (SOff 43 0));
    YP09.mkChunk (-80) (CVal 8 (SOff 42 0)); YP09.mkChunk (-72) (CVal 8 (SOff 41 0));
    YP09.mkChunk (-64) (CVal 8 (SOff 40 0)); YP09.mkChunk (-56) (CVal 8 (SOff 39 0));
    YP09.mkChunk (-48) (CVal 8 (SOff 38 0)); YP09.mkChunk (-40) (CVal 8 (SOff 37 0));
    YP09.mkChunk (-32) (CVal 8 (SOff 36 0)); YP09.mkChunk (-24) (CVal 8 (SOff 35 0));
    YP09.mkChunk (-16) (CVal 8 (SOff 34 0)); YP09.mkChunk (-8) (CVal 8 (SOff 33 0)) ].
Definition arx_mframe_r : YP09.region := YP09.mkRegion (Some 8%nat) (-96) 0 0 0 arx_save_cs.
Definition arx_regions : YP09.smem := [arx_flag_r; arx_frame_r; arx_shadow_r; arx_mframe_r].
Definition arx_facts : facts :=
  mkFacts [(18%nat, mkAF 4096 (2 ^ 47) 6); (32%nat, mkAF 4096 (2 ^ 47) 0);
           (25%nat, mkAF 0x7fff8000 (0x7fff8000 + 2 ^ 44) 3); (8%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition arx_ss : sstate := mkSS AR_CUT_EXIT sr_atoms arx_regions None arx_facts.

(* the flag run, its end state computed; the listing tree is read off the lemma's own type *)
Ltac arx_run_flag RUNF HS HJ :=
  let T := type of RUNF in
  lazymatch T with context [sym_runN_pi ?tpi _ _] =>
  lazymatch type of HS with
  | st_ok_pi _ _ ?E ?ss (restrict (w_H ?W) ?ms) =>
    let r := eval vm_compute in (sym_runN_pi tpi FUEL ss) in
    lazymatch r with
    | (?ss', ?st) =>
      let Hrun := fresh "Hrun" in
      assert (Hrun : sym_runN_pi tpi FUEL ss = (ss', st)) by (vm_compute; reflexivity);
      let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI end in
      eapply (RUNF W FUEL E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun I HJ);
      clear Hrun
    end
  end end.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
(* the image instance: AR's laws, the listing's values, the start-up symbols (the runtime's statics and errno),
   and the image's segments (g_nl is an image byte, a computation) *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HV : LinkVals.
Hypothesis TL : PALib B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : SEGS = tfibsegs.

(* ---- byte views that agree pointwise ---- *)
Lemma arx_mbyte_eq : forall (m m' : word -> option byte) x,
  m' (Z_to_bv 64 x) = m (Z_to_bv 64 x) -> mbyte SEGS m' x = mbyte SEGS m x.
Proof. intros m m' x H. unfold mbyte. rewrite H. reflexivity. Qed.

Lemma arx_writable_eq : forall (m m' : word -> option byte) x,
  m' (Z_to_bv 64 x) = m (Z_to_bv 64 x) -> writable_at SEGS m x -> writable_at SEGS m' x.
Proof. intros m m' x H Hw. unfold writable_at, wview in *. rewrite H. exact Hw. Qed.

Lemma arx_anlk_keep : forall (m m' : word -> option byte) bs, anlk_at SEGS m LA_G_NL bs ->
  (forall x, LA_G_NL <= x < LA_G_NL + NK_SIZE -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
  anlk_at SEGS m' LA_G_NL bs.
Proof.
  intros m m' bs HN Hk. pose proof HN as [[_ Hw] L].
  apply (ar_anlk_move SEGS m m' bs HN); intros x Hx; [apply arx_mbyte_eq; exact (Hk x Hx)|].
  apply (arx_writable_eq m); [exact (Hk x Hx)|].
  replace x with (LA_G_NL + (x - LA_G_NL)) by lia. apply Hw. lia.
Qed.

Lemma arx_abuf_keep : forall (m m' : word -> option byte) p n, abuf SEGS m p n ->
  (forall x, p <= x < p + n -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) -> abuf SEGS m' p n.
Proof.
  intros m m' p n HB Hk. pose proof HB as (junk & L & _ & Hw).
  apply (ar_abuf_move SEGS m m' p n HB); intros x Hx; [apply arx_mbyte_eq; exact (Hk x Hx)|].
  apply (arx_writable_eq m); [exact (Hk x Hx)|].
  replace x with (p + (x - p)) by lia. apply Hw. lia.
Qed.

Lemma arx_acstr_keep : forall (m m' : word -> option byte) p s, acstr_at SEGS m p s ->
  (forall x, p <= x <= p + Z.of_nat (length s) -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) -> acstr_at SEGS m' p s.
Proof.
  intros m m' p s HC Hk. apply (ar_acstr_move SEGS m m' p s HC). intros x Hx. apply arx_mbyte_eq. exact (Hk x Hx).
Qed.

(* g_nl is an image byte outside the runtime's statics and errno (a computation at the image's segments) *)
Lemma arx_gnl_img : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
  intros a Ha. rewrite HSEGS, (ts_owned B TB), (ts_errno B TB). split; [|split].
  - assert (Hb : existsb (fun sg => (Z.of_N (seg_base sg) <=? LA_G_NL) &&
        (LA_G_NL + NK_SIZE <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) tfibsegs = true)
      by (vm_compute; reflexivity).
    apply existsb_exists in Hb as (sg & Hin & Hc). apply andb_true_iff in Hc as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. exists sg. split; [exact Hin | lia].
  - assert (Hb : forallb (fun r => (LA_G_NL + NK_SIZE <=? fst r) || (fst r + snd r <=? LA_G_NL))
        Tfib_owned_static = true) by (vm_compute; reflexivity).
    intros Hex. apply Exists_exists in Hex as (r & Hin & Hr). rewrite forallb_forall in Hb. specialize (Hb r Hin).
    apply orb_true_iff in Hb as [Hb|Hb]; apply Z.leb_le in Hb; unfold in_zr in Hr; lia.
  - assert (He : LA_G_NL + NK_SIZE <= TFIB_ERRNO) by (vm_compute; congruence). lia.
Qed.

(* the machine state at a cut, as the engine's entry shape *)
Lemma arx_ms_eta : forall ms : machine_state, ms_resv ms = None -> ms_svc_pending ms = None ->
  ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr -> ms = mkst (ms_regs ms) (ms_pc_val ms) (ms_mem ms) (ms_rom ms).
Proof. intros [] H1 H2 H3 H4. cbn in *. subst. reflexivity. Qed.

(* a save-slot chunk from the word the cut gives *)
Lemma arx_save_chunk : forall (E : env) (H : word -> bool) (mem : word -> option byte) n sp off (w : word),
  ew E n = w -> rdword (aview SEGS H mem) (sp + off) = Some (bv_unsigned w) ->
  YP09.chunk_ok SEGS E (mrestrict H mem) sp (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
  intros E H mem n sp off w Hn Hr.
  apply (chunk_ok_val SEGS E (mrestrict H mem) sp off 8 (SOff n 0) (bv_unsigned w)).
  - cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - pose proof (bv_unsigned_in_range 64 w) as Q. change (bv_modulus 64) with (2 ^ 64) in Q.
    change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Q.
  - cbn; lia.
  - exact (YCbq.val_mem_of_rdword SEGS _ _ _ _ Hr).
Qed.

(* the extra atoms of the cut's environment: the flag address, then ra, s0, s1, s2 .. s10 as the prologue saved
   them *)
Definition arx_xs (cx : arcx) (fpos : Z) : list word :=
  [w64 (ar_FL cx fpos); getr (ar_regs cx) 1; getr (ar_regs cx) 8; getr (ar_regs cx) 9;
   getr (ar_regs cx) 18; getr (ar_regs cx) 19; getr (ar_regs cx) 20; getr (ar_regs cx) 21; getr (ar_regs cx) 22;
   getr (ar_regs cx) 23; getr (ar_regs cx) 24; getr (ar_regs cx) 25; getr (ar_regs cx) 26].

(* ==========================================================================
   1. The call's context: the facts of the frame, the bytes of the Post, the interface table
   ========================================================================== *)
Section c.
Variable cx : arcx.
Variable fpos : Z.
#[local] Notation F := (ar_F cx fpos).
#[local] Notation SH := (ar_SH cx fpos).
#[local] Notation FL := (ar_FL cx fpos).
#[local] Notation AK := REAC_LINK_ALIAS_READ_AK.
#[local] Notation Eacc := (fun a => ar_E cx a \/ aside_rng (ar_lyc cx) AR_CID fpos a).

Hypothesis HPRE : ar_pre SK B cx.
Hypothesis HNIN : ~ In (AR_CID, fpos) (frames (ar_Sc cx)).
Hypothesis HS1 : exists S1 W1 mem1 md1, AR SEGS B (ar_lyc cx) S1 W1 mem1 md1 /\
  frames S1 = (AR_CID, fpos) :: frames (ar_Sc cx) /\ ablocks B (ar_lyc cx) S1 = ablocks B (ar_lyc cx) (ar_Sc cx).

Lemma arx_pre_j : ajournal_gx SEGS B (ar_G cx) (ar_XO cx) (ar_OUT cx) (ar_STK cx) (ar_sp0 cx) (ar_FP cx)
  (ar_ly cx) (ar_S cx) (ar_W0 cx) (ar_mem0 cx) (ar_md0 cx) (ar_own cx)
  (ar_lyc cx) (ar_Sc cx) (ar_W cx) (ar_memc cx) (ar_mdc cx) (ar_k cx).
Proof. exact (proj1 (proj1 HPRE)). Qed.

Lemma arx_pre_g : gx_ok SEGS B (ar_G cx).
Proof. exact (proj1 (proj2 (proj1 HPRE))). Qed.

Lemma arx_pre_ar : AR SEGS B (ar_lyc cx) (ar_Sc cx) (ar_W cx) (ar_memc cx) (ar_mdc cx).
Proof. exact (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ arx_pre_j). Qed.

(* the call's window: above the allocator's ceiling, below 2 ^ 47 *)
Lemma arx_win : ar_sp cx mod 16 = 0 /\ alloc_ceiling <= ar_sp0 cx - ar_STK cx /\
  ar_sp0 cx - ar_STK cx <= ar_sp cx - AK /\ ar_sp cx <= ar_sp0 cx /\ ar_sp0 cx <= 2 ^ 47.
Proof.
  destruct HPRE as ((HJ & _ & _ & _ & _ & _ & _ & H16 & Hlo & Hhi & _) & _ & _).
  destruct HJ as (HSTK & HXO & (memS & HJi & _) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  unfold ar_sp. repeat split; lia.
Qed.

(* the frame F, from the frame witness *)
Lemma arx_F : 4096 <= F /\ F + 128 <= alloc_ceiling /\ F mod 64 = 0 /\ in_app F 128 /\ off_img F 128 /\
  0 <= fpos < fs_frames AR_CID.
Proof.
  destruct HS1 as (S1 & W1 & mem1 & md1 & HAR & Hfr & _).
  assert (Hin : In (AR_CID, fpos) (frames S1)) by (rewrite Hfr; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS _ S1 W1 mem1 md1 _ _ HAR Hin) as (H1 & H2 & H3).
  destruct (frame_al64 SEGS B _ S1 W1 mem1 md1 _ _ HAR Hin) as (H4 & _).
  pose proof (frm_off_imgP B _ S1 W1 mem1 md1 _ _ HAR Hin) as H5.
  destruct HAR as [M _]. destruct (frame_facts B _ S1 _ _ _ M Hin) as (_ & H6 & _).
  change (fs_frame_bytes AR_CID) with 128 in *. unfold ar_F. exact (conj H1 (conj H2 (conj H4 (conj H3 (conj H5 H6))))).
Qed.

Lemma arx_SH : SH = SHADOW_OFF + F / 8 /\ SH mod 8 = 0 /\ 0x7fff8000 + 512 <= SH /\ SH <= 0x7fff8000 + 2 ^ 44 /\
  SH + 16 <= alloc_ceiling /\ (F + 128 <= SH \/ SH + 16 <= F).
Proof.
  destruct arx_F as (H1 & H2 & H3 & H4 & _). pose proof asan_consts as ((C1a & C1b) & _).
  pose proof (div8_of_mul64 F H3) as (D1 & D2).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in H4.
  assert (HS0 : SHADOW_OFF = 0x7fff8000) by reflexivity.
  unfold ar_SH. rewrite HS0.
  split; [reflexivity|]. split.
  { rewrite D1, Z.add_mod by lia. rewrite (Z.mul_comm 8), Z.mod_mul by lia. reflexivity. }
  split; [lia|]. split; [lia|]. split; [lia|].
  destruct H4 as (_ & [Hl | (Hh1 & Hh2)]); [left | right]; lia.
Qed.

(* the flag byte: below the ceiling, off the image, apart from F and from F's shadow *)
Lemma arx_FL : 4096 <= FL /\ FL < alloc_ceiling /\ ~ in_img SEGS FL /\
  (FL + 1 <= F \/ F + 128 <= FL) /\ (FL + 1 <= SH \/ SH + 16 <= FL).
Proof.
  destruct HS1 as (S1 & W1 & mem1 & md1 & HAR & Hfr & _).
  assert (Hin : In (AR_CID, fpos) (frames S1)) by (rewrite Hfr; left; reflexivity).
  destruct (al_flag _ _ LAWS _ S1 W1 mem1 md1 _ _ HAR Hin) as (_ & Hown & Happ & _).
  destruct (al_frames _ _ LAWS _ S1 W1 mem1 md1 _ _ HAR Hin) as (_ & _ & HFp & HSp).
  destruct (aside_rng_low SK SEGS B LAWS pa_segs_low _ S1 W1 mem1 md1 _ _ FL HAR Hin
    ltac:(right; right; reflexivity)) as (Hc & Hi).
  change (fs_frame_bytes AR_CID) with 128 in HFp, HSp. change (128 / 8) with 16 in HSp.
  unfold in_app in Happ. fold FL in Hown, Happ.
  split; [lia|]. split; [exact Hc|]. split; [exact Hi|]. split.
  - destruct (Z_lt_ge_dec FL F) as [Hlt|Hge]; [left; lia|].
    destruct (Z_lt_ge_dec FL (F + 128)) as [Hlt2|Hge2]; [exfalso | right; lia].
    exact (proj2 (HFp FL ltac:(unfold ar_F in *; lia)) Hown).
  - destruct (Z_lt_ge_dec FL SH) as [Hlt|Hge]; [left; lia|].
    destruct (Z_lt_ge_dec FL (SH + 16)) as [Hlt2|Hge2]; [exfalso | right; lia].
    pose proof (proj2 (HSp (FL - SH) ltac:(lia))) as Hno.
    replace (shadow_addr (frame_addr (ar_lyc cx) AR_CID fpos) + (FL - SH)) with FL in Hno
      by (unfold shadow_addr, ar_SH, ar_F; lia).
    exact (Hno Hown).
Qed.

(* the write set of the contract, byte by byte *)
Lemma arx_E_iff : forall a, ar_E cx a <->
  (LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4) \/
  (aarg (ar_regs cx) 1 <> 0 /\ aarg (ar_regs cx) 1 <= a < aarg (ar_regs cx) 1 + aarg (ar_regs cx) 2) \/
  (aarg (ar_regs cx) 3 <> 0 /\ aarg (ar_regs cx) 3 <= a < aarg (ar_regs cx) 3 + aarg (ar_regs cx) 4).
Proof.
  intros a. unfold ar_E, ar_wr, reac_link_alias_read_awr, aivl, inFP. split.
  - intros (r & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr.
    + left. exact Hr.
    + right; left. revert Hr. destruct (Z.eqb_spec (aarg (ar_regs cx) 1) 0); intros Hr; [lia|].
      split; [assumption | lia].
    + right; right. revert Hr. destruct (Z.eqb_spec (aarg (ar_regs cx) 3) 0); intros Hr; [lia|].
      split; [assumption | lia].
  - intros [H | [(H0 & H) | (H0 & H)]].
    + exists (LA_G_NL, LA_G_NL + NK_N_SENT + 4). split; [left; reflexivity | exact H].
    + exists (aarg (ar_regs cx) 1, aarg (ar_regs cx) 1 + (if aarg (ar_regs cx) 1 =? 0 then 0 else aarg (ar_regs cx) 2)).
      split; [right; left; reflexivity|]. cbn [fst snd]. rewrite (proj2 (Z.eqb_neq _ _) H0). lia.
    + exists (aarg (ar_regs cx) 3, aarg (ar_regs cx) 3 + (if aarg (ar_regs cx) 3 =? 0 then 0 else aarg (ar_regs cx) 4)).
      split; [right; right; left; reflexivity|]. cbn [fst snd]. rewrite (proj2 (Z.eqb_neq _ _) H0). lia.
Qed.

(* g_nl is no byte of the frame (an image byte) *)
Lemma arx_gnl_not_side : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> ~ aside_rng (ar_lyc cx) AR_CID fpos a.
Proof.
  intros a Ha Hs. destruct HS1 as (S1 & W1 & mem1 & md1 & HAR & Hfr & _).
  assert (Hin : In (AR_CID, fpos) (frames S1)) by (rewrite Hfr; left; reflexivity).
  destruct (arx_gnl_img a Ha) as (Hi & _).
  exact (proj2 (aside_rng_low SK SEGS B LAWS pa_segs_low _ S1 W1 mem1 md1 _ _ a HAR Hin Hs) Hi).
Qed.

(* the two buffers are no bytes of the frame: they are bytes of the contract's write set (ajw), in application
   memory (achk) *)
Lemma arx_buf_not_side : forall i j a, (i = 1 /\ j = 2 \/ i = 3 /\ j = 4) ->
  aarg (ar_regs cx) i <> 0 -> 1 <= aarg (ar_regs cx) j ->
  aarg (ar_regs cx) i <= a < aarg (ar_regs cx) i + aarg (ar_regs cx) j ->
  ~ aside_rng (ar_lyc cx) AR_CID fpos a.
Proof.
  intros i j a Hij H0 H1 Ha.
  destruct HPRE as ((_ & HG & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hajw & _) & _ &
    (kbs0 & tab0 & nm0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & KCH & ACH)).
  destruct arx_F as (_ & _ & _ & _ & _ & Hfp).
  assert (HE : ar_E cx a /\ achk SEGS (ar_m0 cx) (aarg (ar_regs cx) i) (aarg (ar_regs cx) j)).
  { destruct Hij as [(-> & ->) | (-> & ->)].
    - split; [apply arx_E_iff; right; left; split; assumption | exact (KCH H0 H1)].
    - split; [apply arx_E_iff; right; right; split; assumption | exact (ACH H0 H1)]. }
  destruct HE as (HE & Hrng & _).
  apply (ajw_not_side SK SEGS B LAWS pa_img_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AR_CID fpos a HG arx_pre_j);
    [unfold AR_CID; lia | exact Hfp | exact HNIN | exact (Hajw a HE) |].
  unfold amem_range in Hrng. arx_c. lia.
Qed.

(* THE INTERFACE TABLE at every memory the walk's akept reaches: its slots are image bytes past the write set, its
   strings are bytes of the read set (apart from g_nl and the buffers by the Pre) *)
Lemma arx_tab_kept : forall kbs tab (W : world SEGS) m kbs',
  anlk_at SEGS (ar_m0 cx) LA_G_NL kbs -> aiftab_at SEGS (ar_m0 cx) LA_G_NL kbs tab ->
  akept SEGS B (ar_lyc cx) (ar_Sc cx) (ar_W cx) (ar_memc cx) W m (ar_sp cx - AK) (ar_sp cx) Eacc ->
  nk_n_if kbs' = nk_n_if kbs -> aiftab_at SEGS (rdW W m) LA_G_NL kbs' tab.
Proof.
  intros kbs tab W m kbs' HNK HIT HK Hn.
  pose proof HPRE as (_ & HRD & (kbs0 & tab0 & nm0 & NK0 & _ & _ & _ & _ & IT0 & _ & _ & _ & _ & _ & _ & TABC & _ & _
    & _ & _ & _ & KF & AF & _ & _)).
  assert (kbs0 = kbs) by exact (ar_anlk_unique SEGS _ _ _ _ NK0 HNK). subst kbs0.
  assert (tab0 = tab) by exact (ar_aiftab_unique SEGS _ _ _ _ IT0 HIT). subst tab0.
  destruct arx_F as (_ & _ & _ & _ & _ & Hfp).
  pose proof HIT as (_ & L80 & EIT).
  pose proof HK as (_ & _ & K3 & _).
  (* a byte of g_nl past the write set is kept *)
  assert (Hgnl : forall x, LA_G_NL + NK_N_SENT + 4 <= x < LA_G_NL + NK_SIZE ->
    mbyte SEGS (rdW W m) x = mbyte SEGS (ar_m0 cx) x).
  { intros x Hx. apply (YCbq.mbyte_of_aview SEGS).
    destruct (arx_gnl_img x ltac:(arx_c; lia)) as (Hi & Ho & He).
    apply (K3 x Hi Ho He). intros [HE | HS].
    - apply arx_E_iff in HE. destruct HE as [HE | [(Hk0 & HE) | (Ha0 & HE)]]; [lia | |].
      + destruct (KF Hk0) as (_ & Hg). unfold apart_gnl in Hg. arx_c. lia.
      + destruct (AF Ha0) as (_ & Hg). unfold apart_gnl in Hg. arx_c. lia.
    - exact (arx_gnl_not_side x ltac:(arx_c; lia) HS). }
  apply (ar_aiftab_keep SEGS (ar_m0 cx) _ kbs kbs' tab HIT Hn).
  - intros x Hx. apply Hgnl. arx_c. lia.
  - intros x Hx. apply Hgnl. arx_c. lia.
  - intros i n2 ix p Hi Hp Hp64 x Hx. apply (YCbq.mbyte_of_aview SEGS).
    destruct (EIT i n2 ix Hi) as (_ & p' & P' & _ & C' & _).
    pose proof (ar_au64_unique SEGS _ _ _ _ Hp P') as Ep. pose proof (ar_acstr_range SEGS _ _ _ C') as Rp.
    rewrite !Z.mod_small in Ep by lia. subst p'.
    assert (Hb : akb SEGS B (ar_lyc cx) (ar_Sc cx) (ar_sp cx - AK) (ar_sp cx) x).
    { apply HRD. right. exists kbs, tab, i, n2, ix, p. exact (conj HNK (conj HIT (conj Hi (conj Hp (conj C' Hx))))). }
    eapply (akept_akb_gx SK SEGS B); [exact arx_pre_j | exact HK | exact Hb |].
    destruct (TABC i n2 ix p Hi Hp) as (_ & Hg & _ & Hk & Ha & _).
    intros [HE | HS].
    + apply arx_E_iff in HE. destruct HE as [HE | [(Hk0 & HE) | (Ha0 & HE)]].
      * unfold apart_gnl in Hg. arx_c. lia.
      * specialize (Hk Hk0 ltac:(lia)). unfold apart in Hk. lia.
      * specialize (Ha Ha0 ltac:(lia)). unfold apart in Ha. lia.
    + exact (akb_not_side SK SEGS B pa_img_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AR_CID fpos x arx_pre_j
        ltac:(unfold AR_CID; lia) Hfp HNIN Hb HS).
Qed.

End c.

(* ==========================================================================
   2. THE EXIT PIECE: from the EXIT cut to the `ret`, and the Post
   ========================================================================== *)
Theorem ar_exit : ar_exit_obl SK B.
Proof.
  intros cx fpos ly3 S3 W3 ms3 md3 HPRE (rcv & Hpc & Ha0 & HB & HPF).
  unfold ar_base in HB. cbv zeta in HB.
  destruct HB as (Hresv & Hsvc & Hrom & Hfregs & Hfcsr & HJ3 & Hfrs3 & Hnin & Hfs3 & Hperm3 &
    (S1 & W1 & mem1 & md1 & HAR1 & Hfrs1 & Eab1) & EFA & R2 & R9 & R8 & R18 & R26 & R25 & R3 & R4 & R27 &
    Hra & Hsv & Hflw & HFp & HSp & HK & Hfds & Hfs & Hro).
  assert (HS1 : exists S1 W1 mem1 md1, AR SEGS B (ar_lyc cx) S1 W1 mem1 md1 /\
    frames S1 = (AR_CID, fpos) :: frames (ar_Sc cx) /\ ablocks B (ar_lyc cx) S1 = ablocks B (ar_lyc cx) (ar_Sc cx))
    by (exists S1, W1, mem1, md1; exact (conj HAR1 (conj Hfrs1 Eab1))).
  pose proof HPRE as ((HJ & HGok & HROD & Hraw & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hside & Hajw & Hnro)
    & HRD & HAP).
  pose proof asan_consts as ((C1a & C1b) & _).
  destruct (arx_win cx HPRE) as (W16 & Wc & Wlo & Whi & W47).
  destruct (arx_F cx fpos HS1) as (F1 & F2 & F3 & F4 & F5 & F6).
  destruct (arx_SH cx fpos HS1) as (SH1 & SH2 & SH3 & SH3b & SH4 & SH5).
  destruct (arx_FL cx fpos HS1) as (FL1 & FL2 & FL3 & FL4 & FL5).
  assert (HK8 : REAC_LINK_ALIAS_READ_AK = 8592) by reflexivity.
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
  assert (Hin3 : In (AR_CID, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
  destruct (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AR_CID fpos HJ3)
    as [_ Ef3].
  destruct (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AR_CID fpos HJ)
    as [_ Efc].
  assert (EFL3 : flag_addr ly3 AR_CID fpos = ar_FL cx fpos) by (rewrite Ef3, <- Efc; reflexivity).
  assert (EFA3 : frame_addr ly3 AR_CID fpos = ar_F cx fpos) by (rewrite EFA; reflexivity).
  destruct (al_flag _ _ LAWS _ _ _ _ _ AR_CID fpos HAR3 Hin3) as (HFLp & _).
  rewrite EFL3 in HFLp.
  pose proof (aj_gx_present SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as Hwin.
  set (sp := ar_sp cx) in *.
  set (F := ar_F cx fpos) in *. set (SH := ar_SH cx fpos) in *. set (FL := ar_FL cx fpos) in *.
  (* ---- the symbolic state at the cut ---- *)
  remember (Eimg (Ereg (ms_regs ms3) (arx_xs cx fpos))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
  assert (EL : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r)
    by (intros n r Hn; rewrite HE; exact (ew_Eimg_Ereg_nat _ _ n r Hn)).
  assert (E8 : ew E 8 = w64 sp) by (rewrite (EL 8%nat (8%bv : bv 5) eq_refl); exact R8).
  assert (E18 : ew E 18 = w64 F) by (rewrite (EL 18%nat (18%bv : bv 5) eq_refl); exact R18).
  assert (E25 : ew E 25 = w64 SH) by (rewrite (EL 25%nat (25%bv : bv 5) eq_refl); exact R25).
  assert (E3 : ew E 3 = getr (ar_regs cx) 3) by (rewrite (EL 3%nat (3%bv : bv 5) eq_refl); exact R3).
  assert (E4 : ew E 4 = getr (ar_regs cx) 4) by (rewrite (EL 4%nat (4%bv : bv 5) eq_refl); exact R4).
  assert (E27 : ew E 27 = getr (ar_regs cx) 27) by (rewrite (EL 27%nat (27%bv : bv 5) eq_refl); exact R27).
  assert (E10 : ew E 10 = w64 rcv) by (rewrite (EL 10%nat (10%bv : bv 5) eq_refl); exact Ha0).
  assert (E32 : ew E 32 = w64 FL) by (rewrite HE; reflexivity).
  assert (E33 : ew E 33 = getr (ar_regs cx) 1) by (rewrite HE; reflexivity).
  assert (E34 : ew E 34 = getr (ar_regs cx) 8) by (rewrite HE; reflexivity).
  assert (E35 : ew E 35 = getr (ar_regs cx) 9) by (rewrite HE; reflexivity).
  assert (E36 : ew E 36 = getr (ar_regs cx) 18) by (rewrite HE; reflexivity).
  assert (E37 : ew E 37 = getr (ar_regs cx) 19) by (rewrite HE; reflexivity).
  assert (E38 : ew E 38 = getr (ar_regs cx) 20) by (rewrite HE; reflexivity).
  assert (E39 : ew E 39 = getr (ar_regs cx) 21) by (rewrite HE; reflexivity).
  assert (E40 : ew E 40 = getr (ar_regs cx) 22) by (rewrite HE; reflexivity).
  assert (E41 : ew E 41 = getr (ar_regs cx) 23) by (rewrite HE; reflexivity).
  assert (E42 : ew E 42 = getr (ar_regs cx) 24) by (rewrite HE; reflexivity).
  assert (E43 : ew E 43 = getr (ar_regs cx) 25) by (rewrite HE; reflexivity).
  assert (E44 : ew E 44 = getr (ar_regs cx) 26) by (rewrite HE; reflexivity).
  assert (U8 : bv_unsigned (ew E 8) = sp) by (rewrite E8; apply unsigned_lit_small; lia).
  assert (U18 : bv_unsigned (ew E 18) = F) by (rewrite E18; apply unsigned_lit_small; lia).
  assert (U25 : bv_unsigned (ew E 25) = SH) by (rewrite E25; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = FL) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (HROK : regs_ok E sr_atoms (ms_regs ms3)) by (rewrite HE; apply regs_ok_Eimg_Ereg).
  clear HE EL.
  (* the bytes the run writes, and that they are bytes of the frame *)
  assert (HWR : forall a, in_wrange E arx_regions a -> (F <= a < F + 8) \/ (SH <= a < SH + 16) \/ a = FL).
  { intros a (r & Hin & Hr). unfold arx_regions in Hin. cbn [In] in Hin.
    destruct Hin as [<- | [<- | [<- | [<- | []]]]];
      unfold arx_flag_r, arx_frame_r, arx_shadow_r, arx_mframe_r in Hr;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      [rewrite U32 in Hr; right; right; lia | rewrite U18 in Hr; left; lia | rewrite U25 in Hr; right; left; lia
      | lia]. }
  assert (HWS : forall a, (F <= a < F + 8) \/ (SH <= a < SH + 16) \/ a = FL -> aside_rng (ar_lyc cx) AR_CID fpos a).
  { intros a [Ha | [Ha | ->]]; unfold aside_rng, in_zr, frame_rng; cbn [fst snd].
    - left. change (fs_frame_bytes AR_CID) with 128. subst F. unfold ar_F in Ha. lia.
    - right; left. change (fs_frame_bytes AR_CID / 8) with 16. rewrite SH1 in Ha. subst F. unfold ar_F in Ha.
      unfold shadow_addr. lia.
    - right; right. reflexivity. }
  (* the state, built at the cut's memory *)
  assert (HS0 : st_ok_pi SEGS VAL E arx_ss (restrict (w_H W3) ms3)).
  { rewrite (arx_ms_eta ms3 Hresv Hsvc Hfregs Hfcsr), Hpc, Hrom, restrict_mkst_fx.
    unfold w64, arx_ss. apply pa_entry_st_ok_full.
    - exact HROK.
    - vm_compute. reflexivity.
    - unfold arx_regions. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
      + unfold region_ok, arx_flag_r.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
        split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
        intros o Ho. replace (FL + o) with FL by lia. apply (YCbq.apresent_writable SEGS). exact HFLp.
      + unfold region_ok, arx_frame_r.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U18.
        split; [lia|]. split; [lia|]. split.
        * intros o Ho. apply (YCbq.apresent_writable SEGS). apply HFp. unfold AR_FB. lia.
        * apply Forall_cons; [|apply Forall_nil].
          apply (chunk_ok_val SEGS E _ F 120 8 (SOff 32 0) FL).
          -- cbn [sv_denot]. rewrite E32, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
          -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
          -- cbn; lia.
          -- unfold AR_FLAGPTR in Hflw. exact (YCbq.val_mem_of_rdword SEGS _ _ _ _ Hflw).
      + unfold region_ok, arx_shadow_r.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U25.
        split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
        intros o Ho. apply (YCbq.apresent_writable SEGS). apply HSp. unfold AR_SHN. lia.
      + unfold region_ok, arx_mframe_r.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U8.
        split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
        unfold arx_save_cs.
        apply Forall_cons; [apply (arx_save_chunk E _ _ 44%nat _ _ _ E44);
          replace (sp + -96) with (sp - 16 - 8 * 10) by lia; exact (Hsv 10 ltac:(lia))|].
        apply Forall_cons; [apply (arx_save_chunk E _ _ 43%nat _ _ _ E43);
          replace (sp + -88) with (sp - 16 - 8 * 9) by lia; exact (Hsv 9 ltac:(lia))|].
        apply Forall_cons; [apply (arx_save_chunk E _ _ 42%nat _ _ _ E42);
          replace (sp + -80) with (sp - 16 - 8 * 8) by lia; exact (Hsv 8 ltac:(lia))|].
        apply Forall_cons; [apply (arx_save_chunk E _ _ 41%nat _ _ _ E41);
          replace (sp + -72) with (sp - 16 - 8 * 7) by lia; exact (Hsv 7 ltac:(lia))|].
        apply Forall_cons; [apply (arx_save_chunk E _ _ 40%nat _ _ _ E40);
          replace (sp + -64) with (sp - 16 - 8 * 6) by lia; exact (Hsv 6 ltac:(lia))|].
        apply Forall_cons; [apply (arx_save_chunk E _ _ 39%nat _ _ _ E39);
          replace (sp + -56) with (sp - 16 - 8 * 5) by lia; exact (Hsv 5 ltac:(lia))|].
        apply Forall_cons; [apply (arx_save_chunk E _ _ 38%nat _ _ _ E38);
          replace (sp + -48) with (sp - 16 - 8 * 4) by lia; exact (Hsv 4 ltac:(lia))|].
        apply Forall_cons; [apply (arx_save_chunk E _ _ 37%nat _ _ _ E37);
          replace (sp + -40) with (sp - 16 - 8 * 3) by lia; exact (Hsv 3 ltac:(lia))|].
        apply Forall_cons; [apply (arx_save_chunk E _ _ 36%nat _ _ _ E36);
          replace (sp + -32) with (sp - 16 - 8 * 2) by lia; exact (Hsv 2 ltac:(lia))|].
        apply Forall_cons; [apply (arx_save_chunk E _ _ 35%nat _ _ _ E35);
          replace (sp + -24) with (sp - 16 - 8 * 1) by lia; exact (Hsv 1 ltac:(lia))|].
        apply Forall_cons; [apply (arx_save_chunk E _ _ 34%nat _ _ _ E34);
          replace (sp + -16) with (sp - 16 - 8 * 0) by lia; exact (Hsv 0 ltac:(lia))|].
        apply Forall_cons; [apply (arx_save_chunk E _ _ 33%nat _ _ _ E33);
          replace (sp + -8) with (sp - 8) by lia; exact Hra|].
        apply Forall_nil.
    - unfold arx_regions, arx_flag_r, arx_frame_r, arx_shadow_r, arx_mframe_r.
      cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U32, U18, U25, U8.
      repeat split; lia.
    - unfold facts_ok, arx_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      split; [|split; exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U18, U32, U25, U8. change (2 ^ 6) with 64. change (2 ^ 3) with 8. change (2 ^ 4) with 16.
      rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia. }
  (* register 26 holds F too: the store `sd a1,0(s10)` lands in the frame region *)
  pose proof (ast_ok_pi_set_reg_fp E arx_ss (restrict (w_H W3) ms3) (26%bv : bv 5) (SOff 18 0) HS0
    ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs restrict]; rewrite E18, Z.add_0_r, R26; unfold w64; rewrite Z_to_bv_bv_unsigned;
          reflexivity)) as HS.
  clear HS0. norm_pi HS.
  (* ---- +0x1fc .. +0x2c4: one plain run with the inline release ---- *)
  arx_run_flag (paj_flag_plain_x SK B LAWS (ar_G cx) HGok (ar_XO cx) (ar_OUT cx)) HS HJ3.
  - unfold AR_CID. lia.
  - intros a Hw. destruct (HWR a Hw) as [Ha | [Ha | ->]].
    + left. apply (aj_gx_awr_frame SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AR_CID fpos a HJ3
        (or_introl eq_refl)).
      left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA3. change (fs_frame_bytes AR_CID) with 128. lia.
    + left. apply (aj_gx_awr_frame SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AR_CID fpos a HJ3
        (or_introl eq_refl)).
      right. unfold in_zr. cbn [fst snd]. rewrite EFA3. change (fs_frame_bytes AR_CID / 8) with 16.
      rewrite SH1 in Ha. unfold shadow_addr. lia.
    + right; right; right. symmetry. exact EFL3.
  - intros msr HSr. rewrite EFL3.
    lazymatch type of HSr with st_ok_pi _ _ ?Ex ?ssx _ =>
      pose proof (st_ok_pi_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR end.
    lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
      pose proof (field_of_region E (ms_mem msr) n _ cs lo hi wlo whi 0 1%N (SLit 0) 0 HR U32
        ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end.
    rewrite Z.add_0_r in V. pose proof (V 0%nat ltac:(lia)) as V0. cbn [Z.of_nat] in V0.
    rewrite Z.add_0_r in V0. exact V0.
  - intros ms' mat' HS' HJ' HF HF' HG'.
    set (md' := with_vm_backing (m_vm_lazy md3) mat' md3) in *.
    prreg HS' (1%bv : bv 5) Q1. prreg HS' (2%bv : bv 5) Q2. prreg HS' (3%bv : bv 5) Q3.
    prreg HS' (4%bv : bv 5) Q4. prreg HS' (8%bv : bv 5) Q8. prreg HS' (9%bv : bv 5) Q9.
    prreg HS' (10%bv : bv 5) Q10.
    prreg HS' (18%bv : bv 5) Q18. prreg HS' (19%bv : bv 5) Q19. prreg HS' (20%bv : bv 5) Q20.
    prreg HS' (21%bv : bv 5) Q21. prreg HS' (22%bv : bv 5) Q22. prreg HS' (23%bv : bv 5) Q23.
    prreg HS' (24%bv : bv 5) Q24. prreg HS' (25%bv : bv 5) Q25. prreg HS' (26%bv : bv 5) Q26.
    prreg HS' (27%bv : bv 5) Q27.
    eapply (paj_ret_at (PL := PL_link) (PI := PI) W3 E _ ms' _ _ HS' eq_refl ltac:(vm_compute; reflexivity)).
    intros mat2.
    set (md2 := with_vm_backing (m_vm_lazy md') mat2 md').
    rewrite Q1, E33. replace (v_jalr (getr (ar_regs cx) 1) 0) with (getr (ar_regs cx) 1) by (symmetry; exact Hraw).
    (* the bytes the run did not write *)
    assert (UNR : forall x, 0 <= x < 2 ^ 64 -> ~ aside_rng (ar_lyc cx) AR_CID fpos x ->
      rdW W3 (ms_mem ms') (Z_to_bv 64 x) = rdW W3 (ms_mem ms3) (Z_to_bv 64 x)).
    { intros x Hx Hn. apply HF'. rewrite unsigned_lit_small by lia. intros Hw. exact (Hn (HWS x (HWR x Hw))). }
    (* the kept clause at the end memory *)
    assert (HK2 : akept SEGS B (ar_lyc cx) (ar_Sc cx) (ar_W cx) (ar_memc cx) W3 (ms_mem ms')
      (sp - REAC_LINK_ALIAS_READ_AK) sp (fun a => ar_E cx a \/ aside_rng (ar_lyc cx) AR_CID fpos a)).
    { apply (akept_step SK SEGS B LAWS pa_segs_low (ar_lyc cx) (ar_Sc cx) (ar_W cx) (ar_memc cx) (ar_mdc cx)
        W3 (ms_mem ms3) W3 (ms_mem ms') (sp - REAC_LINK_ALIAS_READ_AK) sp
        (fun a => ar_E cx a \/ aside_rng (ar_lyc cx) AR_CID fpos a)
        (fun a => ar_E cx a \/ aside_rng (ar_lyc cx) AR_CID fpos a)
        (aside_rng (ar_lyc cx) AR_CID fpos) HARc).
      - lia.
      - lia.
      - exact HK.
      - intros a Ha Hn. apply (YCbq.aview_eq_of SEGS). exact (UNR a Ha Hn).
      - intros a _ Hp. exact (apresent_grows _ _ _ a HG' Hp).
      - intros a Ha. exact Ha.
      - intros a Ha. left. right. exact Ha. }
    unfold ar_post.
    apply (apost_side_gen SK SEGS B LAWS pa_segs_low REAC_LINK_ALIAS_READ_AK 0 (ar_E cx) (ar_G cx) (ar_XO cx)
      (ar_OUT cx) (ar_STK cx) (ar_sp0 cx) (ar_FP cx) (ar_ly cx) (ar_S cx) (ar_W0 cx) (ar_mem0 cx) (ar_md0 cx)
      (ar_own cx) (ar_lyc cx) (ar_Sc cx) (ar_W cx) (ar_memc cx) (ar_mdc cx) (ar_k cx) (ar_regs cx) (ms_regs ms')
      ly3 (stack_free_state AR_CID fpos S3) W3 (ms_mem ms') md2 (ar_k cx) AR_CID fpos S1 W1 mem1 md1).
    + exact HJ.
    + apply (ajournal_gx_materialize SEGS B LAWS pa_segs_low). exact HJ'.
    + lia.
    + subst md2 md'. rewrite !(proj1 (wvb_fds_fs _ _ _)). exact Hfds.
    + subst md2 md'. rewrite !(proj2 (wvb_fds_fs _ _ _)). exact Hfs.
    + apply aregs_preserved_eqs.
      * rewrite Q2, E8. subst sp. unfold w64, ar_sp, spZ. apply Z_to_bv_bv_unsigned.
      * rewrite Q3. exact E3.
      * rewrite Q4. exact E4.
      * rewrite Q8. exact E34.
      * rewrite Q9. exact E35.
      * rewrite Q18. exact E36.
      * rewrite Q19. exact E37.
      * rewrite Q20. exact E38.
      * rewrite Q21. exact E39.
      * rewrite Q22. exact E40.
      * rewrite Q23. exact E41.
      * rewrite Q24. exact E42.
      * rewrite Q25. exact E43.
      * rewrite Q26. exact E44.
      * rewrite Q27. exact E27.
    + exact HAR1.
    + exact Hfrs1.
    + exact Eab1.
    + exact HK2.
    + split; [apply (set_fs_trans S3); [apply set_fs_of_exists; exact Hfs3 | apply stack_free_state_set_fs]|].
      split; [unfold stack_free_state; rewrite ablocks_set_fs; exact Hperm3|].
      (* the Post, from the cut's ar_pf *)
      unfold ar_pf, ar_kind, ar_kn, ar_alias, ar_an, ar_name in HPF.
      intros kbs tab nm NK IT SN. pose proof (HPF kbs tab nm NK IT SN) as HP0. cbv zeta in HP0 |- *.
      destruct HP0 as (Hrc & (kbs' & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15
        & N16) & K1 & K2 & K3 & K4).
      split; [rewrite Q10, E10, Hrc; reflexivity|].
      split.
      { exists kbs'. split.
        { apply (arx_anlk_keep _ _ kbs' N1). intros x Hx. apply UNR; [arx_c; lia|].
          exact (arx_gnl_not_side cx fpos HS1 x Hx). }
        split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [exact N5|].
        split; [exact (arx_tab_kept cx fpos HPRE Hnin HS1 kbs tab W3 (ms_mem ms') kbs' NK IT HK2 N5)|].
        split; [exact N7|]. split; [exact N8|]. split; [exact N9|]. split; [exact N10|]. split; [exact N11|].
        split; [exact N12|]. split; [exact N13|]. split; [exact N14|]. split; [exact N15 | exact N16]. }
      split.
      { intros Hk0 Hkn. pose proof (K1 Hk0 Hkn) as C. apply (arx_acstr_keep _ _ _ _ C). intros x Hx.
        pose proof (ar_acstr_range SEGS _ _ _ C) as Rc.
        pose proof (arx_kind_len tab nm (aarg (ar_regs cx) 2) (aarg (ar_regs cx) 4) (nk_sent kbs) (nk_kstate kbs) Hkn).
        apply UNR; [lia|]. apply (arx_buf_not_side cx fpos HPRE Hnin HS1 1 2); [left; split; reflexivity | exact Hk0 | exact Hkn | lia]. }
      split.
      { intros Ha0' Han. pose proof (K2 Ha0' Han) as C. apply (arx_acstr_keep _ _ _ _ C). intros x Hx.
        pose proof (ar_acstr_range SEGS _ _ _ C) as Rc.
        pose proof (arx_alias_len tab nm (aarg (ar_regs cx) 2) (aarg (ar_regs cx) 4) (nk_sent kbs) (nk_kstate kbs) Han).
        apply UNR; [lia|]. apply (arx_buf_not_side cx fpos HPRE Hnin HS1 3 4); [right; split; reflexivity | exact Ha0' | exact Han | lia]. }
      split.
      { intros Hk0 Hkn. pose proof (K3 Hk0 Hkn) as C. apply (arx_abuf_keep _ _ _ _ C). intros x Hx.
        pose proof C as (junk & Lj & (Ha & Hl & _) & _).
        apply UNR; [lia|]. apply (arx_buf_not_side cx fpos HPRE Hnin HS1 1 2); [left; split; reflexivity | exact Hk0 | exact Hkn | lia]. }
      { intros Ha0' Han. pose proof (K4 Ha0' Han) as C. apply (arx_abuf_keep _ _ _ _ C). intros x Hx.
        pose proof C as (junk & Lj & (Ha & Hl & _) & _).
        apply UNR; [lia|]. apply (arx_buf_not_side cx fpos HPRE Hnin HS1 3 4); [right; split; reflexivity | exact Ha0' | exact Han | lia]. }
Qed.

End b.
End a.

Arguments ar_exit {fx rc} SK {PI}.
About ar_exit.
Print Assumptions ar_exit.
