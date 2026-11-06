(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a segment of reac_headamp_tx_next on fuzz_grant.asan (NextEntry), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/NextEntry.v at a working branch af735a950e2 (blob 8725db69d2a; the walk was ported from blob 7788bf8f6e4 at a working branch afd75724b5b, which differs from it only by 4 added and 0 removed lines, the licence header), restated over image B's listing, addresses and walk layer (lib/B/Prog) against GrantBContracts.v; frame 96 with twelve saved registers, UBSan traps T1 and T2, and the .rodata divisor read at 0x85fa4 (IMG_NEXT_DIV3) *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/NextEntry.v, with its module paths and module names changed; 542 of its 591 lines of code are new or changed and 711 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_link_alias_readExit.v; 1171 of its 1265 lines of code are new or changed and 497 lines of the source are left out. *)
(* reac_link_alias_read (fuzz_link.asan 0x8867c, listing offset AF_reac_link_alias_read) on image A, THE ARMS:
   from the MID cut (+0x118, `beqz s5`) to the SEND cut (+0x180) or to the EXIT cut (+0x1fc). It proves
   reac_link_alias_readDefs.v's obligation `ar_mid_obl` from `ar_send_obl` and `ar_exit_obl`.

   The walk (listing (internal path) (internal record, sha256 7c23ed8f465f)):
     +0x118..+0x130  kind: NULL, cap 0, or the instrumented check and `sb zero,0(s5)`     (arm_kind)
     +0x134..+0x14c  alias: the same, `sb zero,0(s3)`                                    (arm_alias)
     +0x150..+0x16c  a0 := -22; name NULL or name "" go to the EXIT cut                  (arm_tail)
     +0x170..+0x174  fuzz_if_nametoindex(name) (0x826cc), under SRr_bind
     +0x178..+0x17c  index 0: a0 := -19 (+0x1f8), the EXIT cut; else s7 := index, the SEND cut
   Each stretch is one token-engine run from a fresh symbolic state whose atoms are the registers of the
   stretch's start (`armE`). The register of a NULL pointer or of a zero cap is set to the literal 0, a pointer
   that is not NULL gets an atom fact, so the engine decides every `beqz`; each instrumented check is discharged
   by a shadow entry of its pointer (Bx = s8 = SHADOW_OFF). The three stretch starts share one invariant
   (`arm_st`): the cut's registers, g_nl and the read set as the caller had them, the state of each buffer
   (`bkept`: as the caller had it; `bdone`: its NUL stored) and `ar_base`.

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkCall.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_link_alias_read_c nl_talk_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import fuzz_if_nametoindex_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_link_alias_readDefs reac_link_alias_readPost.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_link_alias_readExit reac_link_alias_readSend.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AF0m AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB13.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number -notation-for-abbreviation".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* No global sink_head instance is in scope: every journal below is the Section's SK. *)
Fail Definition sink_head_probe_arm : YI16.sink_head := _.

(* the shadow band the token engine checks against, and its base: s8 holds SHADOW_OFF at the MID cut *)
Definition ArmBspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition ArmBx : sv := SOff 24 0.
Definition ArmF24 : nat * afact := (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0).
Definition arm_kind_r : YP09.region := YP09.mkRegion (Some 21%nat) 0 1 0 1 [].
Definition arm_alias_r : YP09.region := YP09.mkRegion (Some 19%nat) 0 1 0 1 [].

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
(* the image instance: AR's laws, the listing's values (fuzz_if_nametoindex's entry), the start-up symbols (the
   runtime's statics and errno), and the image's segments (g_nl writable, the read-write window: computations) *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HV : LinkVals.
Hypothesis TL : PALib B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : SEGS = tfibsegs.
(* fuzz_if_nametoindex (0x826cc): the proof of fuzz_if_nametoindex_acontract *)
Hypothesis FIFN : fuzz_if_nametoindex_acontract SK SEGS PCAP_RLO PCAP_RHI B.

(* ---- the environment of a stretch: atom r < 32 is register r at the stretch's start ---- *)
Definition armE (R : bvmap 5 word) (xs : list word) : env := Eimg (Ereg R xs).

Lemma armE_img : forall R xs, img_env VAL A_LIM (armE R xs).
Proof. intros R xs. apply Eimg_env. Qed.

Lemma armE_reg : forall R xs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (armE R xs) n = getr R r.
Proof. intros R xs n r Hn. exact (ew_Eimg_Ereg_nat R xs n r Hn). Qed.

Lemma armE_U : forall R xs n (r : bv 5) v, Z.of_nat n = bv_unsigned r -> getr R r = w64 v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (ew (armE R xs) n) = v.
Proof. intros R xs n r v Hn Hr Hv. rewrite (armE_reg R xs n r Hn), Hr. apply unsigned_lit_small. lia. Qed.

Lemma armE_regs : forall R xs, regs_ok (armE R xs) sr_atoms R.
Proof. intros R xs. unfold armE. apply regs_ok_Eimg_Ereg. Qed.

Lemma armE_sv : forall R xs n (r : bv 5), Z.of_nat n = bv_unsigned r -> sv_denot (armE R xs) (SOff n 0) = getr R r.
Proof.
  intros R xs n r Hn. cbn [sv_denot]. rewrite (armE_reg R xs n r Hn), Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.

Lemma armE_x32 : forall R x, ew (armE R [x]) 32 = x.
Proof. intros R x. reflexivity. Qed.

Lemma arm_fact : forall E n lo hi v, bv_unsigned (ew E n) = v -> lo <= v <= hi -> afact_ok E n (mkAF lo hi 0).
Proof. intros E n lo hi v Hv Hr. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Hv, Z.pow_0_r, Z.mod_1_r. lia. Qed.

(* the shape of the machine state at the end of a run *)
Lemma arm_shape : forall (ms : machine_state) R pc m, ms = mkst R pc m (seg_rom SEGS) ->
  ms_resv ms = None /\ ms_svc_pending ms = None /\ ms_rom ms = seg_rom SEGS /\ ms_fregs ms = fp_regs /\
  ms_fcsr ms = fp_csr /\ ms_pc_val ms = pc.
Proof. intros ms R pc m ->. repeat split; reflexivity. Qed.

(* the machine state at a cut, in the shape the run lemmas take *)
Lemma arm_mkst_at : forall (ms : machine_state) pc,
  ms_resv ms = None -> ms_svc_pending ms = None -> ms_rom ms = seg_rom SEGS ->
  ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr -> ms_pc_val ms = w64 (BASE + pc) ->
  ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + pc)) (ms_mem ms) (seg_rom SEGS).
Proof.
  intros ms pc H1 H2 H3 H4 H5 H6.
  transitivity (mkst (ms_regs ms) (ms_pc_val ms) (ms_mem ms) (ms_rom ms));
    [exact (ars_ms_eta ms H1 H2 H4 H5) | rewrite H3, H6; reflexivity].
Qed.

(* ---- writable bytes: a byte the memory shows that is not read-only (a computation at the image's segments) ---- *)
Lemma arm_writable : forall (m : word -> option byte) a, 0 <= a < 2 ^ 64 ->
  mbyte SEGS m a <> None -> ~ in_roP SEGS PCAP_RLO PCAP_RHI a -> writable_at SEGS m a.
Proof.
  intros m a Ha Hm Hro.
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:E.
  - unfold writable_at, wview. rewrite E. discriminate.
  - assert (Hi : in_img SEGS a).
    { apply (seg_rom_in_img SEGS a Ha). unfold mbyte in Hm. rewrite E in Hm. exact Hm. }
    destruct Hi as (sg & Hsg & Hb).
    assert (Hc : forallb (fun s => negb (seg_writable s) || ((0xa1000 <=? Z.of_N (seg_base s)) &&
       (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? pcap_img_end))) tfibsegs = true)
      by (vm_compute; reflexivity).
    rewrite <- HSEGS in Hc. rewrite forallb_forall in Hc. specialize (Hc sg Hsg).
    destruct (seg_writable sg) eqn:Ew.
    + cbn [negb orb] in Hc. apply andb_true_iff in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
      unfold writable_at. rewrite HSEGS. apply AB13.tfib_rw_window. rewrite unsigned_lit_small by lia. lia.
    + exfalso. apply Hro. left. exists sg. split; [exact Hsg | split; [exact Ew | exact Hb]].
Qed.

Lemma arm_vis : forall (W : world SEGS) m x, aview SEGS (w_H W) m x <> None ->
  exists b, mbyte SEGS (rdW W m) x = Some b.
Proof.
  intros W m x H. unfold aview in H.
  destruct (mbyte SEGS (mrestrict (w_H W) m) x) as [b|]; [exists b; reflexivity | exfalso; apply H; reflexivity].
Qed.

Lemma arm_vis_of_mbyte : forall (W : world SEGS) m x b, mbyte SEGS (rdW W m) x = Some b ->
  aview SEGS (w_H W) m x <> None.
Proof. intros W m x b H. unfold aview. rewrite H. discriminate. Qed.

(* a buffer every byte of which the memory shows and none read-only *)
Lemma arm_abuf : forall (W : world SEGS) m p n, 0 <= p -> p + n <= 2 ^ 64 -> 0 <= n ->
  (forall x, p <= x < p + n -> aview SEGS (w_H W) m x <> None) ->
  (forall x, p <= x < p + n -> ~ in_roP SEGS PCAP_RLO PCAP_RHI x) ->
  abuf SEGS (rdW W m) p n.
Proof.
  intros W m p n Hp Hpn Hn Hv Hro.
  exists (abytes_of SEGS (rdW W m) p (Z.to_nat n)).
  pose proof (abytes_of_length SEGS (rdW W m) p (Z.to_nat n)) as L.
  split; [rewrite L; lia|]. split.
  - apply abytes_of_abytes; [exact Hp | lia |]. intros i Hi. apply arm_vis. apply Hv. lia.
  - intros i Hi. rewrite L in Hi. apply arm_writable; [lia | | apply Hro; lia].
    destruct (arm_vis W m (p + i) (Hv (p + i) ltac:(lia))) as (b & Hb). rewrite Hb. discriminate.
Qed.

(* a byte the memory shows, as a one-byte value *)
Lemma arm_val1 : forall (m : word -> option byte) a (b : byte), mbyte SEGS m a = Some b ->
  val_mem SEGS m (a + 0) 1 (bv_unsigned b).
Proof.
  intros m a b H k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite !Z.add_0_r, H. f_equal.
  pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with (2 ^ 8) in Hr.
  unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r, !Z.mod_small by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* ==========================================================================
   1. The call's context
   ========================================================================== *)
Section c.
Variable cx : arcx.
Variable fpos : Z.
#[local] Notation F := (ar_F cx fpos).
#[local] Notation SH := (ar_SH cx fpos).
#[local] Notation AK := REAC_LINK_ALIAS_READ_AK.
#[local] Notation Eacc := (fun a => ar_E cx a \/ aside_rng (ar_lyc cx) AR_CID fpos a).
#[local] Notation AJ ly S W m md :=
  (ajournal_gx SEGS B (ar_G cx) (ar_XO cx) (ar_OUT cx) (ar_STK cx) (ar_sp0 cx) (ar_FP cx)
     (ar_ly cx) (ar_S cx) (ar_W0 cx) (ar_mem0 cx) (ar_md0 cx) ((AR_CID, fpos) :: ar_own cx) ly S W m md (ar_k cx)).
#[local] Notation RD := (reac_link_alias_read_ard SEGS (ar_regs cx) (ar_m0 cx)).
#[local] Notation AA i := (aarg (ar_regs cx) i).

Hypothesis HPRE : ar_pre SK B cx.
Hypothesis HNIN : ~ In (AR_CID, fpos) (frames (ar_Sc cx)).
Hypothesis HS1 : exists S1 W1 mem1 md1, AR SEGS B (ar_lyc cx) S1 W1 mem1 md1 /\
  frames S1 = (AR_CID, fpos) :: frames (ar_Sc cx) /\ ablocks B (ar_lyc cx) S1 = ablocks B (ar_lyc cx) (ar_Sc cx).
Variables (tab : list (list byte * Z)) (kbs : list byte).
Hypothesis HNK : anlk_at SEGS (ar_m0 cx) LA_G_NL kbs.
Hypothesis HIT : aiftab_at SEGS (ar_m0 cx) LA_G_NL kbs tab.

(* the two buffers: (1, 2) is kind and its cap, (3, 4) is alias and its cap *)
Definition arm_buf (i j : Z) : Prop := i = 1 /\ j = 2 \/ i = 3 /\ j = 4.

(* a buffer's bytes as the caller had them, and a buffer whose NUL is stored *)
Definition bkept (i j : Z) (W : world SEGS) (m : word -> option byte) : Prop :=
  AA i <> 0 -> forall a, AA i <= a < AA i + AA j -> aview SEGS (w_H W) m a = aview SEGS (w_H (ar_W cx)) (ar_memc cx) a.
Definition bdone (i j : Z) (W : world SEGS) (m : word -> option byte) : Prop :=
  AA i <> 0 -> 1 <= AA j -> acstr_at SEGS (rdW W m) (AA i) [] /\ abuf SEGS (rdW W m) (AA i) (AA j).

(* the state at the start of each stretch of the arms *)
Definition arm_st (pc : Z) (KB AB : world SEGS -> (word -> option byte) -> Prop)
    (ly : alayout) (S : astate) (W : world SEGS) (ms : machine_state) (md : Model) : Prop :=
  ms_pc_val ms = w64 (BASE + pc) /\
  getr (ms_regs ms) 19 = w64 (ar_alias cx) /\ getr (ms_regs ms) 20 = w64 (ar_an cx) /\
  getr (ms_regs ms) 21 = w64 (ar_kind cx) /\ getr (ms_regs ms) 22 = w64 (ar_kn cx) /\
  getr (ms_regs ms) 23 = w64 (ar_name cx) /\ getr (ms_regs ms) 24 = w64 SHADOW_OFF /\
  ar_gnl_kept cx W (ms_mem ms) /\
  (forall a, RD a -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H (ar_W cx)) (ar_memc cx) a) /\
  KB W (ms_mem ms) /\ AB W (ms_mem ms) /\
  ar_tails cx W (ms_mem ms) /\
  ar_base SK B cx fpos ly S W ms md.

(* the registers a stretch keeps *)
Definition arm_rk (R' R : bvmap 5 word) : Prop :=
  getr R' 2 = getr R 2 /\ getr R' 3 = getr R 3 /\ getr R' 4 = getr R 4 /\ getr R' 8 = getr R 8 /\
  getr R' 9 = getr R 9 /\ getr R' 18 = getr R 18 /\ getr R' 19 = getr R 19 /\ getr R' 20 = getr R 20 /\
  getr R' 21 = getr R 21 /\ getr R' 22 = getr R 22 /\ getr R' 23 = getr R 23 /\ getr R' 24 = getr R 24 /\
  getr R' 25 = getr R 25 /\ getr R' 26 = getr R 26 /\ getr R' 27 = getr R 27.

(* ---- the Pre, piece by piece ---- *)
Lemma arm_pre_buf : forall i j, arm_buf i j -> AA i <> 0 -> 1 <= AA j ->
  abuf SEGS (ar_m0 cx) (AA i) (AA j) /\ achk SEGS (ar_m0 cx) (AA i) (AA j) /\
  apart_frame (ar_regs cx) AK (AA i) (AA j) /\ apart_gnl LA_G_NL (AA i) (AA j) /\
  apart (as_errno B) 4 (AA i) (AA j).
Proof.
  intros i j Hij H0 H1.
  destruct HPRE as (_ & _ & (kbs0 & tab0 & nm0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BK0 & BA0 & _ & _ & _ &
    EK & EA & _ & KF & AF & KCH & ACH)).
  destruct Hij as [(-> & ->) | (-> & ->)].
  - destruct (KF H0) as (Hf & Hg). exact (conj (BK0 H0 H1) (conj (KCH H0 H1) (conj Hf (conj Hg (EK H0))))).
  - destruct (AF H0) as (Hf & Hg). exact (conj (BA0 H0 H1) (conj (ACH H0 H1) (conj Hf (conj Hg (EA H0))))).
Qed.

Lemma arm_buf_E : forall i j a, arm_buf i j -> AA i <> 0 -> AA i <= a < AA i + AA j -> ar_E cx a.
Proof.
  intros i j a Hij H0 Ha. apply (arx_E_iff cx).
  destruct Hij as [(-> & ->) | (-> & ->)]; [right; left | right; right]; split; assumption.
Qed.

Lemma arm_buf_nro : forall i j a, arm_buf i j -> AA i <> 0 -> AA i <= a < AA i + AA j ->
  ~ in_roP SEGS PCAP_RLO PCAP_RHI a.
Proof. intros i j a Hij H0 Ha. exact (ars_pre_nro SK B cx HPRE a (arm_buf_E i j a Hij H0 Ha)). Qed.

(* a byte of a buffer is no byte of g_nl, of the read set, of the frame, of the window, of the other buffer *)
Lemma arm_gnl_out : forall i j a, arm_buf i j -> AA i <> 0 -> 1 <= AA j ->
  LA_G_NL <= a < LA_G_NL + NK_SIZE -> ~ (AA i <= a < AA i + AA j).
Proof.
  intros i j a Hij H0 H1 Ha Hb. destruct (arm_pre_buf i j Hij H0 H1) as (_ & _ & _ & Hg & _).
  unfold apart_gnl in Hg. lia.
Qed.

Lemma arm_rd_out : forall i j a, arm_buf i j -> AA i <> 0 -> 1 <= AA j -> RD a -> ~ (AA i <= a < AA i + AA j).
Proof.
  intros i j a Hij H0 H1 HA Hb.
  destruct HPRE as (_ & _ & (kbs0 & tab0 & nm0 & NK0 & _ & _ & _ & _ & IT0 & _ & _ & _ & SN0 & _ & _ & TABC & NMAP & _)).
  destruct HA as [(Hn0 & s & HC & Ha) | (bs & tb & i' & n2 & ix & p & HN' & HT' & Hi & HU & HC & Ha)].
  - assert (Enm : nm0 = Some s) by (apply (ar_astr_arg_unique SEGS (ar_m0 cx) (aarg (ar_regs cx) 0));
      [exact SN0 | split; assumption]).
    destruct (NMAP s Enm) as (NK1 & NA1).
    destruct Hij as [(-> & ->) | (-> & ->)];
      [specialize (NK1 H0 H1) | specialize (NA1 H0 H1)]; unfold apart in *; lia.
  - assert (bs = kbs0) by exact (ar_anlk_unique SEGS _ _ _ _ HN' NK0). subst bs.
    assert (tb = tab0) by exact (ar_aiftab_unique SEGS _ _ _ _ HT' IT0). subst tb.
    destruct (TABC i' n2 ix p Hi HU) as (_ & _ & _ & BK & BA & _).
    destruct Hij as [(-> & ->) | (-> & ->)];
      [specialize (BK H0 H1) | specialize (BA H0 H1)]; unfold apart in *; lia.
Qed.

Lemma arm_bb : AA 1 <> 0 -> 1 <= AA 2 -> AA 3 <> 0 -> 1 <= AA 4 -> apart (AA 1) (AA 2) (AA 3) (AA 4).
Proof.
  destruct HPRE as (_ & _ & (kbs0 & tab0 & nm0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BB & _)).
  exact BB.
Qed.

(* ---- the invariant across a stretch that writes at most bytes of the buffers ---- *)
Definition arm_X (X : Z -> Prop) : Prop :=
  forall a, X a -> exists i j, arm_buf i j /\ AA i <> 0 /\ 1 <= AA j /\ AA i <= a < AA i + AA j.

Lemma arm_inv_step : forall ly S W m md m' md' (X : Z -> Prop),
  ars_inv SK B cx fpos ly S W m md ->
  AJ ly S W m' md' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  arm_X X ->
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
  m_fds md' = m_fds md -> m_fs md' = m_fs md ->
  ars_inv SK B cx fpos ly S W m' md'.
Proof.
  intros ly S W m md m' md' X (HJ & Hfr & Hfs & Hperm & Hfa & Hra & Hsv & Hfl & HK & Hfds & Hfs' & Hro)
    HJ' UN HX Hpres Efds Efs.
  destruct (ars_win SK B cx HPRE) as (W16 & Wc & Wlo & Whi & W47 & S1lo & S1al).
  pose proof REAC_LINK_ALIAS_READ_AK_val as HK8.
  (* a written byte: of the write set, not of the frame, not of the window, not read-only *)
  assert (HXp : forall a, X a -> ar_E cx a /\ ~ aside_rng (ar_lyc cx) AR_CID fpos a /\
     ~ (ar_sp cx - AK <= a < ar_sp cx) /\ ~ in_roP SEGS PCAP_RLO PCAP_RHI a).
  { intros a HXa. destruct (HX a HXa) as (i & j & Hij & H0 & H1 & Ha).
    destruct (arm_pre_buf i j Hij H0 H1) as (_ & _ & Hf & _).
    split; [exact (arm_buf_E i j a Hij H0 Ha)|].
    split; [exact (arx_buf_not_side SK B LAWS cx fpos HPRE HNIN HS1 i j a Hij H0 H1 Ha)|].
    split; [unfold apart_frame in Hf; change (spZ (ar_regs cx)) with (ar_sp cx) in Hf; lia|].
    exact (arm_buf_nro i j a Hij H0 Ha). }
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (Hstk : forall a, ar_sp cx - 96 <= a < ar_sp cx -> ~ X a).
  { intros a Ha HXa. destruct (HXp a HXa) as (_ & _ & Hw & _). lia. }
  assert (Hflag : forall a, F + 120 <= a < F + 128 -> ~ X a).
  { intros a Ha HXa. destruct (HXp a HXa) as (_ & Hs & _). apply Hs. left. unfold in_zr, frame_rng. cbn [fst snd].
    change (fs_frame_bytes AR_CID) with 128. unfold ar_F in Ha. lia. }
  split; [exact HJ'|]. split; [exact Hfr|]. split; [exact Hfs|]. split; [exact Hperm|]. split; [exact Hfa|].
  split.
  { rewrite <- Hra. apply ars_rdword_eq. intros i Hi. apply UN; [lia | apply Hstk; lia]. }
  split.
  { intros j Hj. rewrite <- (Hsv j Hj). apply ars_rdword_eq. intros i Hi. apply UN; [lia | apply Hstk; lia]. }
  split.
  { rewrite <- Hfl. apply ars_rdword_eq. intros i Hi. unfold AR_FLAGPTR in *.
    destruct (arx_F B LAWS cx fpos HS1) as (F1 & F2 & _).
    apply UN; [lia | apply Hflag; lia]. }
  split.
  { apply (akept_step SK SEGS B LAWS pa_segs_low (ar_lyc cx) (ar_Sc cx) (ar_W cx) (ar_memc cx) (ar_mdc cx) W m W m'
      (ar_sp cx - AK) (ar_sp cx) Eacc Eacc X (ars_pre_ar SK B cx HPRE));
      [lia | lia | exact HK | exact UN | intros a _ Ha; exact (Hpres a Ha) | intros a Ha; exact Ha |].
    intros a HXa. left. left. exact (proj1 (HXp a HXa)). }
  split; [rewrite Efds; exact Hfds|]. split; [rewrite Efs; exact Hfs'|].
  apply (ars_arodata_eq B _ _ _ _ Hro). intros a Hro_a.
  pose proof (pa_img_range a (ars_ro_img HSEGS a Hro_a)) as Hir.
  apply UN; [unfold pcap_img_end, YImgTop.IMG_TOP in Hir; lia|].
  intros HXa. exact (proj2 (proj2 (proj2 (HXp a HXa))) Hro_a).
Qed.

(* ar_base after a stretch that keeps the registers ar_base reads and writes at most bytes of the buffers *)
Lemma arm_base_after : forall (X : Z -> Prop) ly S W ms md ms' md',
  ar_base SK B cx fpos ly S W ms md ->
  ms_resv ms' = None -> ms_svc_pending ms' = None -> ms_rom ms' = seg_rom SEGS ->
  ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  arm_rk (ms_regs ms') (ms_regs ms) ->
  AJ ly S W (ms_mem ms') md' -> m_fds md' = m_fds md -> m_fs md' = m_fs md ->
  (forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) (ms_mem ms') a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a) ->
  arm_X X ->
  ar_base SK B cx fpos ly S W ms' md'.
Proof.
  intros X ly S W ms md ms' md' HB Hr Hs Hrom Hf Hc
    (E2 & E3 & E4 & E8 & E9 & E18 & _ & _ & _ & _ & _ & _ & E25 & E26 & E27) HJ' Efds Efs Hpres UN HX.
  pose proof (ars_inv_of_base SK B cx fpos ly S W ms md HB) as HI.
  pose proof HB as HB0. unfold ar_base in HB0. cbv zeta in HB0.
  destruct HB0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R2 & R9 & R8 & R18 & R26 & R25 & R3 & R4 & R27 & _).
  apply (ars_base_of_inv SK B LAWS cx fpos HNIN HS1 ly S W ms' md' Hr Hs Hrom Hf Hc).
  - rewrite E2. exact R2.
  - rewrite E9. exact R9.
  - rewrite E8. exact R8.
  - rewrite E18. exact R18.
  - rewrite E26. exact R26.
  - rewrite E25. exact R25.
  - rewrite E3. exact R3.
  - rewrite E4. exact R4.
  - rewrite E27. exact R27.
  - exact (arm_inv_step ly S W (ms_mem ms) md (ms_mem ms') md' X HI HJ' UN HX Hpres Efds Efs).
Qed.

(* the cut state after a stretch *)
Lemma arm_after : forall pc pc' (X : Z -> Prop) (KB AB KB' AB' : world SEGS -> (word -> option byte) -> Prop)
    ly S W ms md ms' md',
  arm_st pc KB AB ly S W ms md ->
  ms_resv ms' = None -> ms_svc_pending ms' = None -> ms_rom ms' = seg_rom SEGS ->
  ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr -> ms_pc_val ms' = w64 (BASE + pc') ->
  arm_rk (ms_regs ms') (ms_regs ms) ->
  AJ ly S W (ms_mem ms') md' -> m_fds md' = m_fds md -> m_fs md' = m_fs md ->
  (forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) (ms_mem ms') a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a) ->
  arm_X X ->
  (KB W (ms_mem ms) -> AB W (ms_mem ms) -> KB' W (ms_mem ms') /\ AB' W (ms_mem ms')) ->
  arm_st pc' KB' AB' ly S W ms' md'.
Proof.
  intros pc pc' X KB AB KB' AB' ly S W ms md ms' md'
    (Hpc & R19 & R20 & R21 & R22 & R23 & R24 & HGK & HRK & HKB & HAB & HTL & HB)
    Hr Hs Hrom Hf Hc Hpc' Hrk HJ' Efds Efs Hpres UN HX HKA.
  pose proof Hrk as (_ & _ & _ & _ & _ & _ & E19 & E20 & E21 & E22 & E23 & E24 & _).
  assert (HnX : forall a, 0 <= a < 2 ^ 64 -> (forall i j, arm_buf i j -> AA i <> 0 -> 1 <= AA j ->
     ~ (AA i <= a < AA i + AA j)) -> aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a).
  { intros a Ha Hout. apply UN; [exact Ha|]. intros HXa. destruct (HX a HXa) as (i & j & Hij & H0 & H1 & Hb).
    exact (Hout i j Hij H0 H1 Hb). }
  destruct (HKA HKB HAB) as (HKB' & HAB').
  split; [exact Hpc'|].
  split; [rewrite E19; exact R19|]. split; [rewrite E20; exact R20|]. split; [rewrite E21; exact R21|].
  split; [rewrite E22; exact R22|]. split; [rewrite E23; exact R23|]. split; [rewrite E24; exact R24|].
  split.
  { intros a Ha. rewrite <- (HGK a Ha). apply HnX; [arx_c; lia|]. intros i j Hij H0 H1.
    exact (arm_gnl_out i j a Hij H0 H1 Ha). }
  split.
  { intros a Ha. rewrite <- (HRK a Ha). apply HnX.
    - destruct Ha as [(Hn0 & s & HC & Ha) | (bs & tb & i' & n2 & ix & p & _ & _ & _ & _ & HC & Ha)];
        pose proof (ar_acstr_range SEGS _ _ _ HC); lia.
    - intros i j Hij H0 H1. exact (arm_rd_out i j a Hij H0 H1 Ha). }
  split; [exact HKB'|]. split; [exact HAB'|].
  split.
  { intros p str Hstr a Ha. exact (ar_vis_pres W _ _ a Hpres (HTL p str Hstr a Ha)). }
  exact (arm_base_after X ly S W ms md ms' md' HB Hr Hs Hrom Hf Hc Hrk HJ' Efds Efs Hpres UN HX).
Qed.

(* ---- the buffers' two states across a stretch ---- *)
Lemma bkept_keep : forall i j (W : world SEGS) m m', arm_buf i j ->
  (forall a, AA i <> 0 -> AA i <= a < AA i + AA j -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  bkept i j W m -> bkept i j W m'.
Proof. intros i j W m m' Hij Hk HK H0 a Ha. rewrite (Hk a H0 Ha). exact (HK H0 a Ha). Qed.

Lemma bdone_keep : forall i j (W : world SEGS) m m', arm_buf i j ->
  (forall a, AA i <> 0 -> 1 <= AA j -> AA i <= a < AA i + AA j -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  bdone i j W m -> bdone i j W m'.
Proof.
  intros i j W m m' Hij Hk HD H0 H1. destruct (HD H0 H1) as (HC & HBf).
  pose proof HBf as (junk & L & (Ha & Hl & Hby) & _).
  split.
  - apply (ar_acstr_move SEGS _ _ _ _ HC). intros x Hx. cbn [length Z.of_nat] in Hx.
    apply (YCbq.mbyte_of_aview SEGS). apply Hk; [exact H0 | exact H1 | lia].
  - apply arm_abuf; [lia | lia | lia | |].
    + intros x Hx. rewrite (Hk x H0 H1 Hx).
      pose proof (Hby (Z.to_nat (x - AA i)) ltac:(lia)) as Hb. rewrite Z2Nat.id in Hb by lia.
      replace (AA i + (x - AA i)) with x in Hb by lia.
      destruct (nth_error junk (Z.to_nat (x - AA i))) as [b|] eqn:Eb;
        [exact (arm_vis_of_mbyte W m x b Hb) | apply nth_error_None in Eb; lia].
    + intros x Hx. exact (arm_buf_nro i j x Hij H0 Hx).
Qed.

(* the NUL store: the buffer's first byte is 0, its other bytes the caller's *)
Lemma bdone_of_store : forall i j (W : world SEGS) m m', arm_buf i j -> AA i <> 0 -> 1 <= AA j ->
  bkept i j W m ->
  (forall a, AA i < a < AA i + AA j -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  mbyte SEGS (rdW W m') (AA i) = Some (Z_to_bv 8 0) ->
  bdone i j W m'.
Proof.
  intros i j W m m' Hij H0 H1 HK Hk Hz _ _.
  destruct (arm_pre_buf i j Hij H0 H1) as ((junk & L & (Ha & Hl & Hby) & _) & _).
  split.
  - split; [|intros []]. split; [lia|]. split; [cbn [length app Z.of_nat]; lia|].
    intros k Hk'. cbn [length app] in Hk'. assert (k = 0%nat) by lia. subst k.
    cbn [Z.of_nat nth_error app]. rewrite Z.add_0_r. exact Hz.
  - apply arm_abuf; [lia | lia | lia | |].
    + intros x Hx. destruct (Z.eq_dec x (AA i)) as [->|Hne]; [exact (arm_vis_of_mbyte W m' _ _ Hz)|].
      rewrite (Hk x ltac:(lia)), (HK H0 x Hx).
      pose proof (Hby (Z.to_nat (x - AA i)) ltac:(lia)) as Hb. rewrite Z2Nat.id in Hb by lia.
      replace (AA i + (x - AA i)) with x in Hb by lia.
      destruct (nth_error junk (Z.to_nat (x - AA i))) as [b|] eqn:Eb;
        [exact (arm_vis_of_mbyte (ar_W cx) (ar_memc cx) x b Hb) | apply nth_error_None in Eb; lia].
    + intros x Hx. exact (arm_buf_nro i j x Hij H0 Hx).
Qed.

(* the buffers' NULs across a callee that keeps their bytes *)
Lemma bdone_move : forall i j (W W' : world SEGS) m m', arm_buf i j ->
  (forall a, AA i <> 0 -> 1 <= AA j -> AA i <= a < AA i + AA j -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  bdone i j W m -> bdone i j W' m'.
Proof.
  intros i j W W' m m' Hij Hk HD H0 H1. destruct (HD H0 H1) as (HC & HBf).
  pose proof HBf as (junk & L & (Ha & Hl & Hby) & _).
  split.
  - apply (ar_acstr_move SEGS _ _ _ _ HC). intros x Hx. cbn [length Z.of_nat] in Hx.
    apply (YCbq.mbyte_of_aview SEGS). apply Hk; [exact H0 | exact H1 | lia].
  - apply arm_abuf; [lia | lia | lia | |].
    + intros x Hx. rewrite (Hk x H0 H1 Hx).
      pose proof (Hby (Z.to_nat (x - AA i)) ltac:(lia)) as Hb. rewrite Z2Nat.id in Hb by lia.
      replace (AA i + (x - AA i)) with x in Hb by lia.
      destruct (nth_error junk (Z.to_nat (x - AA i))) as [b|] eqn:Eb;
        [exact (arm_vis_of_mbyte W m x b Hb) | apply nth_error_None in Eb; lia].
    + intros x Hx. exact (arm_buf_nro i j x Hij H0 Hx).
Qed.

(* ---- g_nl at a cut ---- *)
Lemma arm_anlk_now : forall (W : world SEGS) m, ar_gnl_kept cx W m -> anlk_at SEGS (rdW W m) LA_G_NL kbs.
Proof.
  intros W m HG. apply (ar_anlk_move SEGS (ar_m0 cx) _ kbs HNK); intros x Hx.
  - unfold ar_m0. apply (YCbq.mbyte_of_aview SEGS). exact (HG x Hx).
  - pose proof (LA_G_NL_writable (rdW W m) x ltac:(unfold NK_SIZE in Hx; lia)) as Hw.
    rewrite <- HSEGS in Hw. exact Hw.
Qed.

(* ---- THE EXIT CUT'S RESULT CLAUSE for a refusal (reac_link_alias_readPost.v ar_post_refuse, at a cut) ---- *)
Lemma arm_pf_refuse : forall (W : world SEGS) m rcv,
  ar_gnl_kept cx W m ->
  akept SEGS B (ar_lyc cx) (ar_Sc cx) (ar_W cx) (ar_memc cx) W m (ar_sp cx - AK) (ar_sp cx) Eacc ->
  ar_bufs_nul cx W m ->
  (forall nm, astr_arg SEGS (ar_m0 cx) (ar_name cx) nm ->
     read_lib tab nm (ar_kn cx) (ar_an cx) (nk_sent kbs) (nk_kstate kbs) = Rres rcv [] [] (nk_sent kbs) (nk_kstate kbs)) ->
  ar_pf cx rcv W m.
Proof.
  intros W m rcv HG HK HBN HR. unfold ar_pf. intros kbs2 tab2 nm2 NK2 IT2 SN2. cbv zeta.
  assert (kbs2 = kbs) by exact (ar_anlk_unique SEGS _ _ _ _ NK2 HNK). subst kbs2.
  assert (tab2 = tab) by exact (ar_aiftab_unique SEGS _ _ _ _ IT2 HIT). subst tab2.
  rewrite (HR nm2 SN2). cbn [r_rc r_kind r_alias r_reqs r_state].
  pose proof HPRE as (_ & _ & (kbs0 & tab0 & nm0 & NK0 & WF0 & OP0 & _)).
  assert (kbs0 = kbs) by exact (ar_anlk_unique SEGS _ _ _ _ NK0 HNK). subst kbs0.
  pose proof WF0 as WF'. destruct WF' as (W1 & W2 & W3 & _).
  split; [reflexivity|].
  split.
  - exists kbs. split; [exact (arm_anlk_now W m HG)|]. split; [exact WF0|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact (arx_tab_kept SK B LAWS TB HSEGS cx fpos HPRE HNIN HS1 kbs tab W m kbs HNK HIT HK eq_refl)|].
    split; [cbn [k_next nk_kstate]; lia|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [symmetry; apply ar_nk_sent_length; lia|].
    split; [exact OP0|split; [reflexivity|split; [reflexivity|split; [lia|intros _; reflexivity]]]].
  - unfold ar_bufs_nul in HBN. destruct HBN as (BK & BA).
    split; [intros H1 H2; exact (proj1 (BK H1 H2))|].
    split; [intros H1 H2; exact (proj1 (BA H1 H2))|].
    split; [intros H1 H2; exact (proj2 (BK H1 H2))|].
    intros H1 H2; exact (proj2 (BA H1 H2)).
Qed.

Lemma arm_buf_rng : forall i j a, arm_buf i j -> AA i <> 0 -> AA i <= a < AA i + AA j -> 0 <= a < 2 ^ 64.
Proof.
  intros i j a Hij H0 Ha. pose proof (ars_aarg_rng (ar_regs cx) i). pose proof (ars_aarg_rng (ar_regs cx) j).
  destruct (Z_lt_le_dec (AA j) 1) as [Hj|Hj]; [lia|].
  destruct (arm_pre_buf i j Hij H0 Hj) as ((junk & L & (Hp & Hl & _) & _) & _). lia.
Qed.

(* every byte of a buffer is visible at a memory that shows it as the caller had it *)
Lemma arm_buf_vis : forall i j (W : world SEGS) m, arm_buf i j -> AA i <> 0 -> 1 <= AA j -> bkept i j W m ->
  forall x, AA i <= x < AA i + AA j -> aview SEGS (w_H W) m x <> None.
Proof.
  intros i j W m Hij H0 H1 HK x Hx. rewrite (HK H0 x Hx).
  destruct (arm_pre_buf i j Hij H0 H1) as ((junk & L & (Hp & Hl & Hby) & _) & _).
  pose proof (Hby (Z.to_nat (x - AA i)) ltac:(lia)) as Hb. rewrite Z2Nat.id in Hb by lia.
  replace (AA i + (x - AA i)) with x in Hb by lia.
  destruct (nth_error junk (Z.to_nat (x - AA i))) as [b|] eqn:Eb;
    [exact (arm_vis_of_mbyte (ar_W cx) (ar_memc cx) x b Hb) | apply nth_error_None in Eb; lia].
Qed.

(* a callee-saved register *)
Ltac arm_cs := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?r] =>
    let v := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with v end; lia.

(* the registers a token run kept, read off its end state *)
Ltac arm_rk_tac HS :=
  unfold arm_rk; repeat match goal with |- _ /\ _ => split end;
  match goal with |- getr _ ?r = _ =>
    let Q := fresh "Q" in prreg HS r Q; rewrite Q; try (apply armE_reg; reflexivity) end.

(* ==========================================================================
   2. KIND (+0x118 .. +0x134): NULL, cap 0, or the check of the 1-byte store and `sb zero,0(s5)`
   ========================================================================== *)
Lemma arm_kind : forall ly S W msA mdA,
  arm_st AR_CUT_MID (bkept 1 2) (bkept 3 4) ly S W msA mdA ->
  (forall ms' md', arm_st (AF_reac_link_alias_read + 0x134) (bdone 1 2) (bkept 3 4) ly S W ms' md' ->
     SRr SEGS W (mkCfg ms' md') (ar_post SK B cx)) ->
  SRr SEGS W (mkCfg msA mdA) (ar_post SK B cx).
Proof using All.
  intros ly S W msA mdA HA K.
  pose proof HA as (Hpc & R19 & R20 & R21 & R22 & R23 & R24 & HGK & HRK & HKK & HAK & HTL & HB).
  unfold ar_kind, ar_kn, ar_alias, ar_an in R19, R20, R21, R22.
  pose proof HB as HB0. unfold ar_base in HB0. cbv zeta in HB0.
  destruct HB0 as (Hresv & Hsvc & Hrom & Hfregs & Hfcsr & HJ & Hfr & _ & _ & Hperm & _ & Hfa & _).
  pose proof (ars_pre_g SK B cx HPRE) as HGx.
  pose proof (armE_img (ms_regs msA) []) as HEI.
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (Hrms : restrict (w_H W) msA = mkst (ms_regs msA) (Z_to_bv 64 (BASE + AR_CUT_MID))
     (mrestrict (w_H W) (ms_mem msA)) (seg_rom SEGS)).
  { rewrite (arm_mkst_at msA AR_CUT_MID Hresv Hsvc Hrom Hfregs Hfcsr Hpc) at 1. rewrite restrict_mkst_fx. reflexivity. }
  assert (F24 : afact_ok (armE (ms_regs msA) []) 24 (mkAF SHADOW_OFF SHADOW_OFF 0)).
  { apply (arm_fact _ 24 _ _ SHADOW_OFF); [|lia].
    apply (armE_U _ [] 24 (24%bv : bv 5)); [reflexivity | exact R24 | unfold SHADOW_OFF; lia]. }
  assert (U21 : bv_unsigned (ew (armE (ms_regs msA) []) 21) = AA 1)
    by (apply (armE_U _ [] 21 (21%bv : bv 5)); [reflexivity | exact R21 | apply ars_aarg_rng]).
  assert (U22 : bv_unsigned (ew (armE (ms_regs msA) []) 22) = AA 2)
    by (apply (armE_U _ [] 22 (22%bv : bv 5)); [reflexivity | exact R22 | apply ars_aarg_rng]).
  pose proof (ars_aarg_rng (ar_regs cx) 1) as Rk. pose proof (ars_aarg_rng (ar_regs cx) 2) as Rn.
  pose (RUNTO := paj_run_to_x SK B LAWS (ar_G cx) HGx (ar_XO cx) (ar_OUT cx)).
  destruct (Z.eq_dec (AA 1) 0) as [Hk0 | Hk0]; [|destruct (Z.eq_dec (AA 2) 0) as [Hn0 | Hn0]].
  - (* kind = NULL: `beqz s5` taken *)
    assert (HS0 : st_ok_pi SEGS VAL (armE (ms_regs msA) []) (mkSS AR_CUT_MID sr_atoms [] None (mkFacts [ArmF24] [] []))
      (restrict (w_H W) msA)).
    { rewrite Hrms. apply pa_entry_st_ok_full; [apply armE_regs | vm_compute; reflexivity | constructor | exact I |].
      split; [|split; exact I]. cbn [f_atoms atoms_ok ArmF24]. split; [exact F24 | exact I]. }
    pose proof (ast_ok_pi_set_reg_fp (armE (ms_regs msA) []) _ (restrict (w_H W) msA) (21%bv : bv 5) (SLit 0) HS0
      eq_refl ltac:(cbn [ms_regs restrict sv_denot]; rewrite R21, Hk0; reflexivity)) as HS.
    clear HS0.
    assert (SHOK : sh_ok SEGS ArmBx [] (armE (ms_regs msA) []) (mrestrict (w_H W) (ms_mem msA))) by constructor.
    paj_run_to_tok RUNTO HS HJ SHOK ArmBspan (AF_reac_link_alias_read + 0x134); [apply awr_ok_x_nil |].
    assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ False ->
      aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) (ms_mem msA) a).
    { intros a Ha _. apply (ars_frame_aview _ _ (w_H W) (ms_mem msA) (ms_mem ms) a HFr Ha).
      intros (r & Hin & _). cbn [ss_mem] in Hin. destruct Hin. }
    pose proof (st_ok_pi_restrict_mkst (w_H W) _ _ _ HS eq_refl) as Ems. cbn [ss_pc] in Ems.
    destruct (arm_shape _ _ _ _ Ems) as (Sh1 & Sh2 & Sh3 & Sh4 & Sh5 & Sh6).
    apply K.
    apply (arm_after AR_CUT_MID (AF_reac_link_alias_read + 0x134) (fun _ => False) (bkept 1 2) (bkept 3 4)
      (bdone 1 2) (bkept 3 4) ly S W msA mdA ms _ HA Sh1 Sh2 Sh3 Sh4 Sh5).
    + rewrite Sh6. reflexivity.
    + arm_rk_tac HS; rewrite R21, Hk0; reflexivity.
    + exact HJ.
    + exact (proj1 (wvb_fds_fs _ _ _)).
    + exact (proj2 (wvb_fds_fs _ _ _)).
    + intros a Ha. exact (apresent_grows _ _ _ a HG Ha).
    + exact UN.
    + intros a [].
    + intros _ HA1. split; [intros H0; exfalso; exact (H0 Hk0)|].
      apply (bkept_keep 3 4 W (ms_mem msA) (ms_mem ms) (or_intror (conj eq_refl eq_refl))); [|exact HA1].
      intros a H0 Ha. apply UN; [exact (arm_buf_rng 3 4 a (or_intror (conj eq_refl eq_refl)) H0 Ha) | intros []].
  - (* kind given, cap 0: `beqz s6` taken *)
    assert (HS0 : st_ok_pi SEGS VAL (armE (ms_regs msA) [])
      (mkSS AR_CUT_MID sr_atoms [] None (mkFacts [(21%nat, mkAF 1 (2 ^ 64 - 1) 0); ArmF24] [] []))
      (restrict (w_H W) msA)).
    { rewrite Hrms. apply pa_entry_st_ok_full; [apply armE_regs | vm_compute; reflexivity | constructor | exact I |].
      split; [|split; exact I]. cbn [f_atoms atoms_ok ArmF24].
      split; [apply (arm_fact _ 21 _ _ _ U21); lia|]. split; [exact F24 | exact I]. }
    pose proof (ast_ok_pi_set_reg_fp (armE (ms_regs msA) []) _ (restrict (w_H W) msA) (22%bv : bv 5) (SLit 0) HS0
      eq_refl ltac:(cbn [ms_regs restrict sv_denot]; rewrite R22, Hn0; reflexivity)) as HS.
    clear HS0.
    assert (SHOK : sh_ok SEGS ArmBx [] (armE (ms_regs msA) []) (mrestrict (w_H W) (ms_mem msA))) by constructor.
    paj_run_to_tok RUNTO HS HJ SHOK ArmBspan (AF_reac_link_alias_read + 0x134); [apply awr_ok_x_nil |].
    assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ False ->
      aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) (ms_mem msA) a).
    { intros a Ha _. apply (ars_frame_aview _ _ (w_H W) (ms_mem msA) (ms_mem ms) a HFr Ha).
      intros (r & Hin & _). cbn [ss_mem] in Hin. destruct Hin. }
    pose proof (st_ok_pi_restrict_mkst (w_H W) _ _ _ HS eq_refl) as Ems. cbn [ss_pc] in Ems.
    destruct (arm_shape _ _ _ _ Ems) as (Sh1 & Sh2 & Sh3 & Sh4 & Sh5 & Sh6).
    apply K.
    apply (arm_after AR_CUT_MID (AF_reac_link_alias_read + 0x134) (fun _ => False) (bkept 1 2) (bkept 3 4)
      (bdone 1 2) (bkept 3 4) ly S W msA mdA ms _ HA Sh1 Sh2 Sh3 Sh4 Sh5).
    + rewrite Sh6. reflexivity.
    + arm_rk_tac HS; rewrite R22, Hn0; reflexivity.
    + exact HJ.
    + exact (proj1 (wvb_fds_fs _ _ _)).
    + exact (proj2 (wvb_fds_fs _ _ _)).
    + intros a Ha. exact (apresent_grows _ _ _ a HG Ha).
    + exact UN.
    + intros a [].
    + intros _ HA1. split; [intros _ H1; exfalso; lia|].
      apply (bkept_keep 3 4 W (ms_mem msA) (ms_mem ms) (or_intror (conj eq_refl eq_refl))); [|exact HA1].
      intros a H0 Ha. apply UN; [exact (arm_buf_rng 3 4 a (or_intror (conj eq_refl eq_refl)) H0 Ha) | intros []].
  - (* kind and its cap given: the check, then kind[0] := 0 *)
    assert (Hn1 : 1 <= AA 2) by lia.
    destruct (arm_pre_buf 1 2 (or_introl (conj eq_refl eq_refl)) Hk0 Hn1)
      as ((junk & L & (Hp & Hl & Hby) & _) & (Hmr & Hra & Hhv) & Hfrm & Hgn & Her).
    assert (E21 : U (armE (ms_regs msA) []) (SOff 21 0) = AA 1).
    { unfold U. rewrite (armE_sv _ [] 21 (21%bv : bv 5) eq_refl), R21. apply unsigned_lit_small. lia. }
    assert (EBx : U (armE (ms_regs msA) []) ArmBx = SHADOW_OFF).
    { unfold U, ArmBx. rewrite (armE_sv _ [] 24 (24%bv : bv 5) eq_refl), R24. apply unsigned_lit_small.
      unfold SHADOW_OFF. lia. }
    pose proof (arm_buf_vis 1 2 W (ms_mem msA) (or_introl (conj eq_refl eq_refl)) Hk0 Hn1 HKK) as Hkv.
    assert (Hkw : writable_at SEGS (rdW W (ms_mem msA)) (AA 1)).
    { apply arm_writable; [lia | | exact (arm_buf_nro 1 2 (AA 1) (or_introl (conj eq_refl eq_refl)) Hk0 ltac:(lia))].
      destruct (arm_vis W (ms_mem msA) (AA 1) (Hkv (AA 1) ltac:(lia))) as (b & Hb). rewrite Hb. discriminate. }
    pose proof (ars_inv_of_base SK B cx fpos ly S W msA mdA HB) as HI.
    destruct (ars_shadow_at SK B LAWS TB cx fpos HPRE HNIN HS1 tab kbs HNK HIT ly S W (ms_mem msA) mdA (AA 1) (AA 2)
      HI ltac:(lia)
      (fun x Hx => ars_buf_sclass SK B LAWS cx HPRE tab kbs HNK HIT 1 2 x (or_introl (conj eq_refl eq_refl)) Hk0 Hn1 Hx)
      Hra Hhv) as (HRA & _).
    assert (HS : st_ok_pi SEGS VAL (armE (ms_regs msA) []) (mkSS AR_CUT_MID sr_atoms [arm_kind_r] None
        (mkFacts [(21%nat, mkAF 1 (2 ^ 47 - 1) 0); (22%nat, mkAF 1 (2 ^ 64 - 1) 0); ArmF24] [] []))
        (restrict (w_H W) msA)).
    { rewrite Hrms. apply pa_entry_st_ok_full; [apply armE_regs | vm_compute; reflexivity | | cbn; tauto |].
      - constructor; [|constructor]. unfold region_ok, arm_kind_r.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U21.
        split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. assert (o = 0) by lia. subst o. rewrite Z.add_0_r. exact Hkw.
      - split; [|split; exact I]. cbn [f_atoms atoms_ok ArmF24].
        split; [apply (arm_fact _ 21 _ _ _ U21); unfold amem_range in Hmr; arx_c; lia|].
        split; [apply (arm_fact _ 22 _ _ _ U22); lia|]. split; [exact F24 | exact I]. }
    assert (SHOK : sh_ok SEGS ArmBx [mkSHE 21 0 1] (armE (ms_regs msA) []) (mrestrict (w_H W) (ms_mem msA))).
    { constructor; [|constructor]. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite EBx, E21. split.
      - intros x Hx. apply HRA. lia.
      - intros a Ha. cbn [Z.min Z.max] in Ha. unfold amem_range in Hmr. arx_c. unfold SHADOW_OFF. lia. }
    paj_run_to_tok RUNTO HS HJ SHOK ArmBspan (AF_reac_link_alias_read + 0x134).
    { intros a (r & Hin & Hr). cbn [In ss_mem] in Hin. destruct Hin as [<- | []].
      unfold arm_kind_r in Hr. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite U21 in Hr.
      assert (Ea : a = AA 1) by lia. subst a.
      exact (ajw_mono B (ar_G cx) (ar_XO cx) (ar_OUT cx) (ar_STK cx) (ar_sp0 cx) (ar_FP cx) (ar_ly cx) (ar_S cx)
        (ar_lyc cx) (ar_Sc cx) (ar_own cx) ly S ((AR_CID, fpos) :: ar_own cx) (AA 1)
        (ars_pre_ajw SK B cx HPRE (AA 1) (arm_buf_E 1 2 (AA 1) (or_introl (conj eq_refl eq_refl)) Hk0 ltac:(lia)))
        (fun b0 m0 Hb => Permutation_in _ (Permutation_sym Hperm) Hb) (fun x Hx => or_intror Hx) Hfa). }
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as HR.
    lazymatch type of HR with region_ok _ ?Ex _ _ =>
      assert (U21' : bv_unsigned (ew Ex 21) = AA 1) by exact U21 end.
    pose proof (field_of_region _ _ _ _ _ _ _ _ _ 0 1%N (SLit 0) 0 HR U21' ltac:(left; reflexivity) eq_refl
      ltac:(cbn; lia) ltac:(cbn; lia)) as V.
    assert (Hz : mbyte SEGS (rdW W (ms_mem ms)) (AA 1) = Some (Z_to_bv 8 0)).
    { pose proof (V 0%nat ltac:(cbn; lia)) as V0. cbn [Z.of_nat ms_mem restrict] in V0. rewrite !Z.add_0_r in V0.
      exact V0. }
    assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (a = AA 1) ->
      aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) (ms_mem msA) a).
    { intros a Ha Hne. apply (ars_frame_aview _ _ (w_H W) (ms_mem msA) (ms_mem ms) a HFr Ha).
      intros (r & Hin & Hr). cbn [ss_mem In] in Hin. destruct Hin as [<- | []].
      unfold arm_kind_r in Hr. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite U21 in Hr. lia. }
    pose proof (st_ok_pi_restrict_mkst (w_H W) _ _ _ HS eq_refl) as Ems. cbn [ss_pc] in Ems.
    destruct (arm_shape _ _ _ _ Ems) as (Sh1 & Sh2 & Sh3 & Sh4 & Sh5 & Sh6).
    apply K.
    apply (arm_after AR_CUT_MID (AF_reac_link_alias_read + 0x134) (fun a => a = AA 1) (bkept 1 2) (bkept 3 4)
      (bdone 1 2) (bkept 3 4) ly S W msA mdA ms _ HA Sh1 Sh2 Sh3 Sh4 Sh5).
    + rewrite Sh6. reflexivity.
    + arm_rk_tac HS.
    + exact HJ.
    + exact (proj1 (wvb_fds_fs _ _ _)).
    + exact (proj2 (wvb_fds_fs _ _ _)).
    + intros a Ha. exact (apresent_grows _ _ _ a HG Ha).
    + exact UN.
    + intros a ->. exists 1, 2. split; [left; split; reflexivity|]. split; [exact Hk0|]. split; [exact Hn1|]. lia.
    + intros HK1 HA1. split.
      * apply (bdone_of_store 1 2 W (ms_mem msA) (ms_mem ms) (or_introl (conj eq_refl eq_refl)) Hk0 Hn1 HK1);
          [|exact Hz].
        intros a Ha. apply UN; lia.
      * apply (bkept_keep 3 4 W (ms_mem msA) (ms_mem ms) (or_intror (conj eq_refl eq_refl))); [|exact HA1].
        intros a H0 Ha. apply UN; [exact (arm_buf_rng 3 4 a (or_intror (conj eq_refl eq_refl)) H0 Ha)|].
        intros ->. destruct (Z_lt_le_dec (AA 4) 1) as [Hj|Hj]; [lia|].
        pose proof (arm_bb Hk0 Hn1 H0 Hj) as Hap. unfold apart in Hap. lia.
Qed.

(* ==========================================================================
   3. ALIAS (+0x134 .. +0x150): NULL, cap 0, or the check of the 1-byte store and `sb zero,0(s3)`
   ========================================================================== *)
Lemma arm_alias : forall ly S W msA mdA,
  arm_st (AF_reac_link_alias_read + 0x134) (bdone 1 2) (bkept 3 4) ly S W msA mdA ->
  (forall ms' md', arm_st (AF_reac_link_alias_read + 0x150) (bdone 1 2) (bdone 3 4) ly S W ms' md' ->
     SRr SEGS W (mkCfg ms' md') (ar_post SK B cx)) ->
  SRr SEGS W (mkCfg msA mdA) (ar_post SK B cx).
Proof using All.
  intros ly S W msA mdA HA K.
  pose proof HA as (Hpc & R19 & R20 & R21 & R22 & R23 & R24 & HGK & HRK & HKD & HKK & HTL & HB).
  unfold ar_kind, ar_kn, ar_alias, ar_an in R19, R20, R21, R22.
  pose proof HB as HB0. unfold ar_base in HB0. cbv zeta in HB0.
  destruct HB0 as (Hresv & Hsvc & Hrom & Hfregs & Hfcsr & HJ & Hfr & _ & _ & Hperm & _ & Hfa & _).
  pose proof (ars_pre_g SK B cx HPRE) as HGx.
  pose proof (armE_img (ms_regs msA) []) as HEI.
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (Hrms : restrict (w_H W) msA = mkst (ms_regs msA) (Z_to_bv 64 (BASE + (AF_reac_link_alias_read + 0x134)))
     (mrestrict (w_H W) (ms_mem msA)) (seg_rom SEGS)).
  { rewrite (arm_mkst_at msA (AF_reac_link_alias_read + 0x134) Hresv Hsvc Hrom Hfregs Hfcsr Hpc) at 1. rewrite restrict_mkst_fx. reflexivity. }
  assert (F24 : afact_ok (armE (ms_regs msA) []) 24 (mkAF SHADOW_OFF SHADOW_OFF 0)).
  { apply (arm_fact _ 24 _ _ SHADOW_OFF); [|lia].
    apply (armE_U _ [] 24 (24%bv : bv 5)); [reflexivity | exact R24 | unfold SHADOW_OFF; lia]. }
  assert (U19 : bv_unsigned (ew (armE (ms_regs msA) []) 19) = AA 3)
    by (apply (armE_U _ [] 19 (19%bv : bv 5)); [reflexivity | exact R19 | apply ars_aarg_rng]).
  assert (U20 : bv_unsigned (ew (armE (ms_regs msA) []) 20) = AA 4)
    by (apply (armE_U _ [] 20 (20%bv : bv 5)); [reflexivity | exact R20 | apply ars_aarg_rng]).
  pose proof (ars_aarg_rng (ar_regs cx) 3) as Ra. pose proof (ars_aarg_rng (ar_regs cx) 4) as Rb.
  pose (RUNTO := paj_run_to_x SK B LAWS (ar_G cx) HGx (ar_XO cx) (ar_OUT cx)).
  destruct (Z.eq_dec (AA 3) 0) as [Hk0 | Hk0]; [|destruct (Z.eq_dec (AA 4) 0) as [Hn0 | Hn0]].
  - (* alias = NULL: `beqz s3` taken *)
    assert (HS0 : st_ok_pi SEGS VAL (armE (ms_regs msA) []) (mkSS (AF_reac_link_alias_read + 0x134) sr_atoms [] None (mkFacts [ArmF24] [] []))
      (restrict (w_H W) msA)).
    { rewrite Hrms. apply pa_entry_st_ok_full; [apply armE_regs | vm_compute; reflexivity | constructor | exact I |].
      split; [|split; exact I]. cbn [f_atoms atoms_ok ArmF24]. split; [exact F24 | exact I]. }
    pose proof (ast_ok_pi_set_reg_fp (armE (ms_regs msA) []) _ (restrict (w_H W) msA) (19%bv : bv 5) (SLit 0) HS0
      eq_refl ltac:(cbn [ms_regs restrict sv_denot]; rewrite R19, Hk0; reflexivity)) as HS.
    clear HS0.
    assert (SHOK : sh_ok SEGS ArmBx [] (armE (ms_regs msA) []) (mrestrict (w_H W) (ms_mem msA))) by constructor.
    paj_run_to_tok RUNTO HS HJ SHOK ArmBspan (AF_reac_link_alias_read + 0x150); [apply awr_ok_x_nil |].
    assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ False ->
      aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) (ms_mem msA) a).
    { intros a Ha _. apply (ars_frame_aview _ _ (w_H W) (ms_mem msA) (ms_mem ms) a HFr Ha).
      intros (r & Hin & _). cbn [ss_mem] in Hin. destruct Hin. }
    pose proof (st_ok_pi_restrict_mkst (w_H W) _ _ _ HS eq_refl) as Ems. cbn [ss_pc] in Ems.
    destruct (arm_shape _ _ _ _ Ems) as (Sh1 & Sh2 & Sh3 & Sh4 & Sh5 & Sh6).
    apply K.
    apply (arm_after (AF_reac_link_alias_read + 0x134) (AF_reac_link_alias_read + 0x150) (fun _ => False) (bdone 1 2) (bkept 3 4)
      (bdone 1 2) (bdone 3 4) ly S W msA mdA ms _ HA Sh1 Sh2 Sh3 Sh4 Sh5).
    + rewrite Sh6. reflexivity.
    + arm_rk_tac HS; rewrite R19, Hk0; reflexivity.
    + exact HJ.
    + exact (proj1 (wvb_fds_fs _ _ _)).
    + exact (proj2 (wvb_fds_fs _ _ _)).
    + intros a Ha. exact (apresent_grows _ _ _ a HG Ha).
    + exact UN.
    + intros a [].
    + intros HK1 _. split; [|intros H0; exfalso; exact (H0 Hk0)].
      apply (bdone_keep 1 2 W (ms_mem msA) (ms_mem ms) (or_introl (conj eq_refl eq_refl))); [|exact HK1].
      intros a H0 H1 Ha. apply UN; [exact (arm_buf_rng 1 2 a (or_introl (conj eq_refl eq_refl)) H0 Ha) | intros []].
  - (* alias given, cap 0: `beqz s4` taken *)
    assert (HS0 : st_ok_pi SEGS VAL (armE (ms_regs msA) [])
      (mkSS (AF_reac_link_alias_read + 0x134) sr_atoms [] None (mkFacts [(19%nat, mkAF 1 (2 ^ 64 - 1) 0); ArmF24] [] []))
      (restrict (w_H W) msA)).
    { rewrite Hrms. apply pa_entry_st_ok_full; [apply armE_regs | vm_compute; reflexivity | constructor | exact I |].
      split; [|split; exact I]. cbn [f_atoms atoms_ok ArmF24].
      split; [apply (arm_fact _ 19 _ _ _ U19); lia|]. split; [exact F24 | exact I]. }
    pose proof (ast_ok_pi_set_reg_fp (armE (ms_regs msA) []) _ (restrict (w_H W) msA) (20%bv : bv 5) (SLit 0) HS0
      eq_refl ltac:(cbn [ms_regs restrict sv_denot]; rewrite R20, Hn0; reflexivity)) as HS.
    clear HS0.
    assert (SHOK : sh_ok SEGS ArmBx [] (armE (ms_regs msA) []) (mrestrict (w_H W) (ms_mem msA))) by constructor.
    paj_run_to_tok RUNTO HS HJ SHOK ArmBspan (AF_reac_link_alias_read + 0x150); [apply awr_ok_x_nil |].
    assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ False ->
      aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) (ms_mem msA) a).
    { intros a Ha _. apply (ars_frame_aview _ _ (w_H W) (ms_mem msA) (ms_mem ms) a HFr Ha).
      intros (r & Hin & _). cbn [ss_mem] in Hin. destruct Hin. }
    pose proof (st_ok_pi_restrict_mkst (w_H W) _ _ _ HS eq_refl) as Ems. cbn [ss_pc] in Ems.
    destruct (arm_shape _ _ _ _ Ems) as (Sh1 & Sh2 & Sh3 & Sh4 & Sh5 & Sh6).
    apply K.
    apply (arm_after (AF_reac_link_alias_read + 0x134) (AF_reac_link_alias_read + 0x150) (fun _ => False) (bdone 1 2) (bkept 3 4)
      (bdone 1 2) (bdone 3 4) ly S W msA mdA ms _ HA Sh1 Sh2 Sh3 Sh4 Sh5).
    + rewrite Sh6. reflexivity.
    + arm_rk_tac HS; rewrite R20, Hn0; reflexivity.
    + exact HJ.
    + exact (proj1 (wvb_fds_fs _ _ _)).
    + exact (proj2 (wvb_fds_fs _ _ _)).
    + intros a Ha. exact (apresent_grows _ _ _ a HG Ha).
    + exact UN.
    + intros a [].
    + intros HK1 _. split; [|intros _ H1; exfalso; lia].
      apply (bdone_keep 1 2 W (ms_mem msA) (ms_mem ms) (or_introl (conj eq_refl eq_refl))); [|exact HK1].
      intros a H0 H1 Ha. apply UN; [exact (arm_buf_rng 1 2 a (or_introl (conj eq_refl eq_refl)) H0 Ha) | intros []].
  - (* alias and its cap given: the check, then alias[0] := 0 *)
    assert (Hn1 : 1 <= AA 4) by lia.
    destruct (arm_pre_buf 3 4 (or_intror (conj eq_refl eq_refl)) Hk0 Hn1)
      as ((junk & L & (Hp & Hl & Hby) & _) & (Hmr & Hra & Hhv) & Hfrm & Hgn & Her).
    assert (E19 : U (armE (ms_regs msA) []) (SOff 19 0) = AA 3).
    { unfold U. rewrite (armE_sv _ [] 19 (19%bv : bv 5) eq_refl), R19. apply unsigned_lit_small. lia. }
    assert (EBx : U (armE (ms_regs msA) []) ArmBx = SHADOW_OFF).
    { unfold U, ArmBx. rewrite (armE_sv _ [] 24 (24%bv : bv 5) eq_refl), R24. apply unsigned_lit_small.
      unfold SHADOW_OFF. lia. }
    pose proof (arm_buf_vis 3 4 W (ms_mem msA) (or_intror (conj eq_refl eq_refl)) Hk0 Hn1 HKK) as Hkv.
    assert (Hkw : writable_at SEGS (rdW W (ms_mem msA)) (AA 3)).
    { apply arm_writable; [lia | | exact (arm_buf_nro 3 4 (AA 3) (or_intror (conj eq_refl eq_refl)) Hk0 ltac:(lia))].
      destruct (arm_vis W (ms_mem msA) (AA 3) (Hkv (AA 3) ltac:(lia))) as (b & Hb). rewrite Hb. discriminate. }
    pose proof (ars_inv_of_base SK B cx fpos ly S W msA mdA HB) as HI.
    destruct (ars_shadow_at SK B LAWS TB cx fpos HPRE HNIN HS1 tab kbs HNK HIT ly S W (ms_mem msA) mdA (AA 3) (AA 4)
      HI ltac:(lia)
      (fun x Hx => ars_buf_sclass SK B LAWS cx HPRE tab kbs HNK HIT 3 4 x (or_intror (conj eq_refl eq_refl)) Hk0 Hn1 Hx)
      Hra Hhv) as (HRA & _).
    assert (HS : st_ok_pi SEGS VAL (armE (ms_regs msA) []) (mkSS (AF_reac_link_alias_read + 0x134) sr_atoms [arm_alias_r] None
        (mkFacts [(19%nat, mkAF 1 (2 ^ 47 - 1) 0); (20%nat, mkAF 1 (2 ^ 64 - 1) 0); ArmF24] [] []))
        (restrict (w_H W) msA)).
    { rewrite Hrms. apply pa_entry_st_ok_full; [apply armE_regs | vm_compute; reflexivity | | cbn; tauto |].
      - constructor; [|constructor]. unfold region_ok, arm_alias_r.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U19.
        split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. assert (o = 0) by lia. subst o. rewrite Z.add_0_r. exact Hkw.
      - split; [|split; exact I]. cbn [f_atoms atoms_ok ArmF24].
        split; [apply (arm_fact _ 19 _ _ _ U19); unfold amem_range in Hmr; arx_c; lia|].
        split; [apply (arm_fact _ 20 _ _ _ U20); lia|]. split; [exact F24 | exact I]. }
    assert (SHOK : sh_ok SEGS ArmBx [mkSHE 19 0 1] (armE (ms_regs msA) []) (mrestrict (w_H W) (ms_mem msA))).
    { constructor; [|constructor]. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite EBx, E19. split.
      - intros x Hx. apply HRA. lia.
      - intros a Ha. cbn [Z.min Z.max] in Ha. unfold amem_range in Hmr. arx_c. unfold SHADOW_OFF. lia. }
    paj_run_to_tok RUNTO HS HJ SHOK ArmBspan (AF_reac_link_alias_read + 0x150).
    { intros a (r & Hin & Hr). cbn [In ss_mem] in Hin. destruct Hin as [<- | []].
      unfold arm_alias_r in Hr. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite U19 in Hr.
      assert (Ea : a = AA 3) by lia. subst a.
      exact (ajw_mono B (ar_G cx) (ar_XO cx) (ar_OUT cx) (ar_STK cx) (ar_sp0 cx) (ar_FP cx) (ar_ly cx) (ar_S cx)
        (ar_lyc cx) (ar_Sc cx) (ar_own cx) ly S ((AR_CID, fpos) :: ar_own cx) (AA 3)
        (ars_pre_ajw SK B cx HPRE (AA 3) (arm_buf_E 3 4 (AA 3) (or_intror (conj eq_refl eq_refl)) Hk0 ltac:(lia)))
        (fun b0 m0 Hb => Permutation_in _ (Permutation_sym Hperm) Hb) (fun x Hx => or_intror Hx) Hfa). }
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as HR.
    lazymatch type of HR with region_ok _ ?Ex _ _ =>
      assert (U19' : bv_unsigned (ew Ex 19) = AA 3) by exact U19 end.
    pose proof (field_of_region _ _ _ _ _ _ _ _ _ 0 1%N (SLit 0) 0 HR U19' ltac:(left; reflexivity) eq_refl
      ltac:(cbn; lia) ltac:(cbn; lia)) as V.
    assert (Hz : mbyte SEGS (rdW W (ms_mem ms)) (AA 3) = Some (Z_to_bv 8 0)).
    { pose proof (V 0%nat ltac:(cbn; lia)) as V0. cbn [Z.of_nat ms_mem restrict] in V0. rewrite !Z.add_0_r in V0.
      exact V0. }
    assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (a = AA 3) ->
      aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) (ms_mem msA) a).
    { intros a Ha Hne. apply (ars_frame_aview _ _ (w_H W) (ms_mem msA) (ms_mem ms) a HFr Ha).
      intros (r & Hin & Hr). cbn [ss_mem In] in Hin. destruct Hin as [<- | []].
      unfold arm_alias_r in Hr. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite U19 in Hr. lia. }
    pose proof (st_ok_pi_restrict_mkst (w_H W) _ _ _ HS eq_refl) as Ems. cbn [ss_pc] in Ems.
    destruct (arm_shape _ _ _ _ Ems) as (Sh1 & Sh2 & Sh3 & Sh4 & Sh5 & Sh6).
    apply K.
    apply (arm_after (AF_reac_link_alias_read + 0x134) (AF_reac_link_alias_read + 0x150) (fun a => a = AA 3) (bdone 1 2) (bkept 3 4)
      (bdone 1 2) (bdone 3 4) ly S W msA mdA ms _ HA Sh1 Sh2 Sh3 Sh4 Sh5).
    + rewrite Sh6. reflexivity.
    + arm_rk_tac HS.
    + exact HJ.
    + exact (proj1 (wvb_fds_fs _ _ _)).
    + exact (proj2 (wvb_fds_fs _ _ _)).
    + intros a Ha. exact (apresent_grows _ _ _ a HG Ha).
    + exact UN.
    + intros a ->. exists 3, 4. split; [right; split; reflexivity|]. split; [exact Hk0|]. split; [exact Hn1|]. lia.
    + intros HK1 HA1. split.
      * apply (bdone_keep 1 2 W (ms_mem msA) (ms_mem ms) (or_introl (conj eq_refl eq_refl))); [|exact HK1].
        intros a H0 H1 Ha. apply UN; [exact (arm_buf_rng 1 2 a (or_introl (conj eq_refl eq_refl)) H0 Ha)|].
        intros ->. pose proof (arm_bb H0 H1 Hk0 Hn1) as Hap. unfold apart in Hap. lia.
      * apply (bdone_of_store 3 4 W (ms_mem msA) (ms_mem ms) (or_intror (conj eq_refl eq_refl)) Hk0 Hn1 HA1);
          [|exact Hz].
        intros a Ha. apply UN; lia.
Qed.

(* ==========================================================================
   4. THE TAIL (+0x150 .. ): the three refusals and the call of fuzz_if_nametoindex
   ========================================================================== *)
Hypothesis EXIT : ar_exit_obl SK B.
Hypothesis SENDO : ar_send_obl SK B.

(* the EXIT cut after a stretch from +0x150 that writes no memory and leaves a0 = rcv *)
Lemma arm_exit_at : forall ly S W msA mdA ms md rcv,
  arm_st (AF_reac_link_alias_read + 0x150) (bdone 1 2) (bdone 3 4) ly S W msA mdA ->
  ms_resv ms = None -> ms_svc_pending ms = None -> ms_rom ms = seg_rom SEGS -> ms_fregs ms = fp_regs ->
  ms_fcsr ms = fp_csr -> ms_pc_val ms = w64 (BASE + AR_CUT_EXIT) ->
  arm_rk (ms_regs ms) (ms_regs msA) -> getr (ms_regs ms) 10 = w64 rcv ->
  AJ ly S W (ms_mem ms) md -> m_fds md = m_fds mdA -> m_fs md = m_fs mdA ->
  (forall a, apresent (w_H W) (ms_mem msA) a -> apresent (w_H W) (ms_mem ms) a) ->
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) (ms_mem msA) a) ->
  (forall nm, astr_arg SEGS (ar_m0 cx) (ar_name cx) nm ->
     read_lib tab nm (ar_kn cx) (ar_an cx) (nk_sent kbs) (nk_kstate kbs) = Rres rcv [] [] (nk_sent kbs) (nk_kstate kbs)) ->
  SRr SEGS W (mkCfg ms md) (ar_post SK B cx).
Proof.
  intros ly S W msA mdA ms md rcv HA Sh1 Sh2 Sh3 Sh4 Sh5 Hpc' Hrk R10 HJ' Efds Efs Hpres UN HR.
  pose proof HA as (Hpc & R19 & R20 & R21 & R22 & R23 & R24 & HGK & HRK & HKD & HAD & HTL & HB).
  assert (HB' : ar_base SK B cx fpos ly S W ms md).
  { exact (arm_base_after (fun _ => False) ly S W msA mdA ms md HB Sh1 Sh2 Sh3 Sh4 Sh5 Hrk HJ' Efds Efs Hpres
      (fun a Ha _ => UN a Ha) (fun a Hx => match Hx with end)). }
  apply (EXIT cx fpos ly S W ms md HPRE). exists rcv.
  split; [exact Hpc'|]. split; [exact R10|]. split; [exact HB'|].
  pose proof HB' as HB0. unfold ar_base in HB0. cbv zeta in HB0.
  destruct HB0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & HK & _).
  apply (arm_pf_refuse W (ms_mem ms) rcv); [| exact HK | | exact HR].
  - intros a Ha. rewrite <- (HGK a Ha). apply UN. arx_c. lia.
  - split.
    + exact (bdone_keep 1 2 W (ms_mem msA) (ms_mem ms) (or_introl (conj eq_refl eq_refl))
        (fun a H0 H1 Ha => UN a (arm_buf_rng 1 2 a (or_introl (conj eq_refl eq_refl)) H0 Ha)) HKD).
    + exact (bdone_keep 3 4 W (ms_mem msA) (ms_mem ms) (or_intror (conj eq_refl eq_refl))
        (fun a H0 H1 Ha => UN a (arm_buf_rng 3 4 a (or_intror (conj eq_refl eq_refl)) H0 Ha)) HAD).
Qed.

Ltac arm_rg HS n r Q := prreg HS r Q; rewrite (armE_reg _ _ n r eq_refl) in Q.

(* after fuzz_if_nametoindex (+0x178): index 0 goes to the EXIT cut with -19, else s7 := index, the SEND cut *)
Lemma arm_after_call : forall ly2 S2 (W2 : world SEGS) (R2 : bvmap 5 word) m2 md2 sn,
  ars_inv SK B cx fpos ly2 S2 W2 m2 md2 ->
  getr R2 2 = w64 (ar_sp1 cx) -> getr R2 9 = w64 (ar_sp1 cx) -> getr R2 8 = w64 (ar_sp cx) ->
  getr R2 18 = w64 F -> getr R2 26 = w64 F -> getr R2 25 = w64 SH ->
  getr R2 3 = getr (ar_regs cx) 3 -> getr R2 4 = getr (ar_regs cx) 4 -> getr R2 27 = getr (ar_regs cx) 27 ->
  getr R2 19 = w64 (ar_alias cx) -> getr R2 20 = w64 (ar_an cx) -> getr R2 21 = w64 (ar_kind cx) ->
  getr R2 22 = w64 (ar_kn cx) -> getr R2 24 = w64 SHADOW_OFF ->
  getr R2 10 = w64 (index_of tab sn) ->
  ar_gnl_kept cx W2 m2 -> ar_bufs_nul cx W2 m2 ->
  acstr_at SEGS (ar_m0 cx) (ar_name cx) sn -> ar_name cx <> 0 -> sn <> [] ->
  SRr SEGS W2 (mkCfg (mkst R2 (Z_to_bv 64 (BASE + (AF_reac_link_alias_read + 0x178))) m2 (seg_rom SEGS)) md2)
    (ar_post SK B cx).
Proof using All.
  intros ly2 S2 W2 R2 m2 md2 sn HI E2 E9 E8 E18 E26 E25 E3 E4 E27 E19 E20 E21 E22 E24 E10 HGK HBN HSN HN0 HSNE.
  pose proof HI as (HJ & _).
  pose proof (ars_pre_g SK B cx HPRE) as HGx.
  pose proof (armE_img R2 []) as HEI.
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (HIX : 0 <= index_of tab sn < 2 ^ 31).
  { apply ar_index_of_range. intros i n ix Hi. destruct HIT as (_ & _ & EIT). exact (proj1 (EIT i n ix Hi)). }
  assert (F24 : afact_ok (armE R2 []) 24 (mkAF SHADOW_OFF SHADOW_OFF 0)).
  { apply (arm_fact _ 24 _ _ SHADOW_OFF); [|lia].
    apply (armE_U _ [] 24 (24%bv : bv 5)); [reflexivity | exact E24 | unfold SHADOW_OFF; lia]. }
  pose (RUNTO := paj_run_to_x SK B LAWS (ar_G cx) HGx (ar_XO cx) (ar_OUT cx)).
  assert (HS0 : forall G, facts_ok (armE R2 []) G ->
    st_ok_pi SEGS VAL (armE R2 []) (mkSS (AF_reac_link_alias_read + 0x178) sr_atoms [] None G)
      (restrict (w_H W2) (mkst R2 (Z_to_bv 64 (BASE + (AF_reac_link_alias_read + 0x178))) m2 (seg_rom SEGS)))).
  { intros G HG. rewrite restrict_mkst_fx.
    apply pa_entry_st_ok_full; [apply armE_regs | vm_compute; reflexivity | constructor | exact I | exact HG]. }
  assert (SHOK : sh_ok SEGS ArmBx [] (armE R2 []) (mrestrict (w_H W2) m2)) by constructor.
  (* the memory and the invariant at the end of the stretch, which writes nothing *)
  assert (Hend : forall (ms : machine_state) md' rs, frame_of (armE R2 []) rs (mrestrict (w_H W2) m2) (rdW W2 (ms_mem ms)) ->
    (forall a, ~ in_wrange (armE R2 []) rs a) ->
    AJ ly2 S2 W2 (ms_mem ms) md' -> m_fds md' = m_fds md2 -> m_fs md' = m_fs md2 ->
    mem_grows (mrestrict (w_H W2) m2) (rdW W2 (ms_mem ms)) ->
    (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) m2 a) /\
    ars_inv SK B cx fpos ly2 S2 W2 (ms_mem ms) md').
  { intros ms md' rs HFr Hnw HJ' Efds Efs HG.
    assert (UN : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) m2 a).
    { intros a Ha. exact (ars_frame_aview _ _ (w_H W2) m2 (ms_mem ms) a HFr Ha (Hnw a)). }
    split; [exact UN|].
    exact (arm_inv_step ly2 S2 W2 m2 md2 (ms_mem ms) md' (fun _ => False) HI HJ' (fun a Ha _ => UN a Ha)
      (fun a Hx => match Hx with end) (fun a Ha => apresent_grows _ _ _ a HG Ha) Efds Efs). }
  destruct (Z.eq_dec (index_of tab sn) 0) as [Hi0 | Hi0].
  - (* index 0: +0x1f8 a0 := -19, the EXIT cut *)
    pose proof (ast_ok_pi_set_reg_fp (armE R2 []) _ _ (10%bv : bv 5) (SLit 0)
      (HS0 (mkFacts [ArmF24] [] []) ltac:(split; [cbn [f_atoms atoms_ok ArmF24]; split; [exact F24 | exact I] | split; exact I]))
      eq_refl ltac:(cbn [ms_regs restrict mkst sv_denot]; rewrite E10, Hi0; reflexivity)) as HS.
    paj_run_to_tok RUNTO HS HJ SHOK ArmBspan AR_CUT_EXIT; [apply awr_ok_x_nil |].
    lazymatch goal with |- SRr _ _ (mkCfg _ ?md) _ => set (md' := md) end.
    destruct (Hend ms md' _ HFr ltac:(intros a (r & Hin & _); cbn [ss_mem] in Hin; destruct Hin) HJ
      ltac:(subst md'; exact (proj1 (wvb_fds_fs _ _ _))) ltac:(subst md'; exact (proj2 (wvb_fds_fs _ _ _))) HG)
      as (UN & HI').
    pose proof (st_ok_pi_restrict_mkst (w_H W2) _ _ _ HS eq_refl) as Ems. cbn [ss_pc] in Ems.
    destruct (arm_shape _ _ _ _ Ems) as (Sh1 & Sh2 & Sh3 & Sh4 & Sh5 & Sh6).
    arm_rg HS 2%nat (2%bv : bv 5) Q2. arm_rg HS 9%nat (9%bv : bv 5) Q9. arm_rg HS 8%nat (8%bv : bv 5) Q8.
    arm_rg HS 18%nat (18%bv : bv 5) Q18. arm_rg HS 26%nat (26%bv : bv 5) Q26. arm_rg HS 25%nat (25%bv : bv 5) Q25.
    arm_rg HS 3%nat (3%bv : bv 5) Q3. arm_rg HS 4%nat (4%bv : bv 5) Q4. arm_rg HS 27%nat (27%bv : bv 5) Q27.
    assert (HB' : ar_base SK B cx fpos ly2 S2 W2 ms md').
    { apply (ars_base_of_inv SK B LAWS cx fpos HNIN HS1 ly2 S2 W2 ms md' Sh1 Sh2 Sh3 Sh4 Sh5);
        [rewrite Q2; exact E2 | rewrite Q9; exact E9 | rewrite Q8; exact E8 | rewrite Q18; exact E18
        | rewrite Q26; exact E26 | rewrite Q25; exact E25 | rewrite Q3; exact E3 | rewrite Q4; exact E4
        | rewrite Q27; exact E27 | exact HI']. }
    apply (EXIT cx fpos ly2 S2 W2 ms md' HPRE). exists (-19).
    split; [rewrite Sh6; reflexivity|].
    split; [prreg HS (10%bv : bv 5) Q10; rewrite Q10; apply bv_eq; reflexivity|].
    split; [exact HB'|].
    pose proof HI' as (_ & _ & _ & _ & _ & _ & _ & _ & HK' & _).
    apply (arm_pf_refuse W2 (ms_mem ms) (-19)); [| exact HK' | |].
    + intros a Ha. rewrite <- (HGK a Ha). apply UN. arx_c. lia.
    + destruct HBN as (BK & BA). split.
      * exact (bdone_move 1 2 W2 W2 m2 (ms_mem ms) (or_introl (conj eq_refl eq_refl))
          (fun a H0 H1 Ha => UN a (arm_buf_rng 1 2 a (or_introl (conj eq_refl eq_refl)) H0 Ha)) BK).
      * exact (bdone_move 3 4 W2 W2 m2 (ms_mem ms) (or_intror (conj eq_refl eq_refl))
          (fun a H0 H1 Ha => UN a (arm_buf_rng 3 4 a (or_intror (conj eq_refl eq_refl)) H0 Ha)) BA).
    + intros nm Hnm. assert (nm = Some sn) by (apply (ar_astr_arg_unique SEGS _ _ _ _ Hnm); split; assumption).
      subst nm. rewrite (ar_read_lib_nodev tab sn (ar_kn cx) (ar_an cx) (nk_sent kbs) (nk_kstate kbs) HSNE Hi0).
      reflexivity.
  - (* the index: s7 := a0, the SEND cut *)
    assert (U10 : bv_unsigned (ew (armE R2 []) 10) = index_of tab sn)
      by (apply (armE_U _ [] 10 (10%bv : bv 5)); [reflexivity | exact E10 | lia]).
    pose proof (HS0 (mkFacts [(10%nat, mkAF 1 (2 ^ 31 - 1) 0); ArmF24] [] [])
      ltac:(split; [cbn [f_atoms atoms_ok ArmF24]; split; [apply (arm_fact _ 10 _ _ _ U10); lia | split; [exact F24 | exact I]]
        | split; exact I])) as HS.
    paj_run_to_tok RUNTO HS HJ SHOK ArmBspan AR_CUT_SEND; [apply awr_ok_x_nil |].
    lazymatch goal with |- SRr _ _ (mkCfg _ ?md) _ => set (md' := md) end.
    destruct (Hend ms md' _ HFr ltac:(intros a (r & Hin & _); cbn [ss_mem] in Hin; destruct Hin) HJ
      ltac:(subst md'; exact (proj1 (wvb_fds_fs _ _ _))) ltac:(subst md'; exact (proj2 (wvb_fds_fs _ _ _))) HG)
      as (UN & HI').
    pose proof (st_ok_pi_restrict_mkst (w_H W2) _ _ _ HS eq_refl) as Ems. cbn [ss_pc] in Ems.
    destruct (arm_shape _ _ _ _ Ems) as (Sh1 & Sh2 & Sh3 & Sh4 & Sh5 & Sh6).
    arm_rg HS 2%nat (2%bv : bv 5) Q2. arm_rg HS 9%nat (9%bv : bv 5) Q9. arm_rg HS 8%nat (8%bv : bv 5) Q8.
    arm_rg HS 18%nat (18%bv : bv 5) Q18. arm_rg HS 26%nat (26%bv : bv 5) Q26. arm_rg HS 25%nat (25%bv : bv 5) Q25.
    arm_rg HS 3%nat (3%bv : bv 5) Q3. arm_rg HS 4%nat (4%bv : bv 5) Q4. arm_rg HS 27%nat (27%bv : bv 5) Q27.
    arm_rg HS 19%nat (19%bv : bv 5) Q19. arm_rg HS 20%nat (20%bv : bv 5) Q20. arm_rg HS 21%nat (21%bv : bv 5) Q21.
    arm_rg HS 22%nat (22%bv : bv 5) Q22. arm_rg HS 24%nat (24%bv : bv 5) Q24. prreg HS (23%bv : bv 5) Q23. rewrite (armE_reg _ _ 10 (10%bv : bv 5) eq_refl) in Q23.
    assert (HB' : ar_base SK B cx fpos ly2 S2 W2 ms md').
    { apply (ars_base_of_inv SK B LAWS cx fpos HNIN HS1 ly2 S2 W2 ms md' Sh1 Sh2 Sh3 Sh4 Sh5);
        [rewrite Q2; exact E2 | rewrite Q9; exact E9 | rewrite Q8; exact E8 | rewrite Q18; exact E18
        | rewrite Q26; exact E26 | rewrite Q25; exact E25 | rewrite Q3; exact E3 | rewrite Q4; exact E4
        | rewrite Q27; exact E27 | exact HI']. }
    apply (SENDO cx fpos ly2 S2 W2 ms md' HPRE). exists sn, tab, kbs.
    split; [rewrite Sh6; reflexivity|]. split; [exact HNK|]. split; [exact HIT|]. split; [exact HSN|].
    split; [exact HN0|]. split; [exact HSNE|]. split; [exact Hi0|].
    split; [rewrite Q23; exact E10|]. split; [rewrite Q19; exact E19|]. split; [rewrite Q20; exact E20|].
    split; [rewrite Q21; exact E21|]. split; [rewrite Q22; exact E22|]. split; [rewrite Q24; exact E24|].
    split.
    { intros a Ha. rewrite <- (HGK a Ha). apply UN. arx_c. lia. }
    split; [|exact HB'].
    destruct HBN as (BK & BA). split.
    + exact (bdone_move 1 2 W2 W2 m2 (ms_mem ms) (or_introl (conj eq_refl eq_refl))
        (fun a H0 H1 Ha => UN a (arm_buf_rng 1 2 a (or_introl (conj eq_refl eq_refl)) H0 Ha)) BK).
    + exact (bdone_move 3 4 W2 W2 m2 (ms_mem ms) (or_intror (conj eq_refl eq_refl))
        (fun a H0 H1 Ha => UN a (arm_buf_rng 3 4 a (or_intror (conj eq_refl eq_refl)) H0 Ha)) BA).
Qed.

(* the stretch from +0x150: name NULL, name "", or the check, the first byte and fuzz_if_nametoindex *)
Lemma arm_tail : forall ly S W msA mdA,
  arm_st (AF_reac_link_alias_read + 0x150) (bdone 1 2) (bdone 3 4) ly S W msA mdA ->
  SRr SEGS W (mkCfg msA mdA) (ar_post SK B cx).
Proof using All.
  intros ly S W msA mdA HA.
  pose proof HA as (Hpc & R19 & R20 & R21 & R22 & R23 & R24 & HGK & HRK & HKD & HAD & HTL & HB).
  unfold ar_name in R23.
  pose proof HB as HB0. unfold ar_base in HB0. cbv zeta in HB0.
  destruct HB0 as (Hresv & Hsvc & Hrom & Hfregs & Hfcsr & HJ & Hfr & _ & _ & Hperm & _ & Hfa & R2b & R9b & R8b & R18b
    & R26b & R25b & R3b & R4b & R27b & _).
  pose proof HPRE as (HAPRE & HRD & (kbs0 & tab0 & nm0 & NK0 & WF0 & OP0 & O10 & C10 & IT0 & RA0 & HV0 & ERR0 & SN0 &
    BK0 & BA0 & TABC & NMAP & BB & EK & EA & NMC & KF & AF & KCH & ACH)).
  assert (kbs0 = kbs) by exact (ar_anlk_unique SEGS _ _ _ _ NK0 HNK). subst kbs0.
  assert (tab0 = tab) by exact (ar_aiftab_unique SEGS _ _ _ _ IT0 HIT). subst tab0.
  pose proof (ars_pre_g SK B cx HPRE) as HGx.
  pose proof asan_consts as ((C1a & C1b) & _).
  pose proof (ars_win SK B cx HPRE) as (W16 & Wc & Wlo & Whi & W47 & S1lo & S1al).
  pose proof REAC_LINK_ALIAS_READ_AK_val as HK8.
  pose proof (ars_aarg_rng (ar_regs cx) 0) as Rn0.
  assert (Hrms : restrict (w_H W) msA = mkst (ms_regs msA) (Z_to_bv 64 (BASE + (AF_reac_link_alias_read + 0x150)))
     (mrestrict (w_H W) (ms_mem msA)) (seg_rom SEGS)).
  { rewrite (arm_mkst_at msA (AF_reac_link_alias_read + 0x150) Hresv Hsvc Hrom Hfregs Hfcsr Hpc) at 1.
    rewrite restrict_mkst_fx. reflexivity. }
  assert (F24 : forall xs, afact_ok (armE (ms_regs msA) xs) 24 (mkAF SHADOW_OFF SHADOW_OFF 0)).
  { intros xs. apply (arm_fact _ 24 _ _ SHADOW_OFF); [|lia].
    apply (armE_U _ xs 24 (24%bv : bv 5)); [reflexivity | exact R24 | unfold SHADOW_OFF; lia]. }
  assert (U23 : forall xs, bv_unsigned (ew (armE (ms_regs msA) xs) 23) = AA 0)
    by (intros xs; apply (armE_U _ xs 23 (23%bv : bv 5)); [reflexivity | exact R23 | exact Rn0]).
  assert (E23 : forall xs, U (armE (ms_regs msA) xs) (SOff 23 0) = AA 0).
  { intros xs. unfold U. rewrite (armE_sv _ xs 23 (23%bv : bv 5) eq_refl), R23. apply unsigned_lit_small. exact Rn0. }
  assert (EBx : forall xs, U (armE (ms_regs msA) xs) ArmBx = SHADOW_OFF).
  { intros xs. unfold U, ArmBx. rewrite (armE_sv _ xs 24 (24%bv : bv 5) eq_refl), R24. apply unsigned_lit_small.
    unfold SHADOW_OFF. lia. }
  pose proof (ars_inv_of_base SK B cx fpos ly S W msA mdA HB) as HI0.
  (* the memory at the end of a stretch that writes nothing *)
  assert (Hnw : forall (ms : machine_state) rs xs,
    frame_of (armE (ms_regs msA) xs) rs (mrestrict (w_H W) (ms_mem msA)) (rdW W (ms_mem ms)) ->
    (forall a, ~ in_wrange (armE (ms_regs msA) xs) rs a) ->
    forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) (ms_mem msA) a).
  { intros ms rs xs HFr Hn a Ha. exact (ars_frame_aview _ _ (w_H W) (ms_mem msA) (ms_mem ms) a HFr Ha (Hn a)). }
  pose (RUNTO := paj_run_to_x SK B LAWS (ar_G cx) HGx (ar_XO cx) (ar_OUT cx)).
  pose proof SN0 as SN0a.
  destruct nm0 as [sn|].
  2: { (* the name is NULL: `beqz s7` taken, a0 = -22 *)
    cbn [astr_arg] in SN0.
    pose proof (armE_img (ms_regs msA) []) as HEI.
    assert (HS0 : st_ok_pi SEGS VAL (armE (ms_regs msA) [])
      (mkSS (AF_reac_link_alias_read + 0x150) sr_atoms [] None (mkFacts [ArmF24] [] [])) (restrict (w_H W) msA)).
    { rewrite Hrms. apply pa_entry_st_ok_full; [apply armE_regs | vm_compute; reflexivity | constructor | exact I |].
      split; [|split; exact I]. cbn [f_atoms atoms_ok ArmF24]. split; [exact (F24 []) | exact I]. }
    pose proof (ast_ok_pi_set_reg_fp (armE (ms_regs msA) []) _ (restrict (w_H W) msA) (23%bv : bv 5) (SLit 0) HS0
      eq_refl ltac:(cbn [ms_regs restrict sv_denot]; rewrite R23, SN0; reflexivity)) as HS.
    clear HS0.
    assert (SHOK : sh_ok SEGS ArmBx [] (armE (ms_regs msA) []) (mrestrict (w_H W) (ms_mem msA))) by constructor.
    paj_run_to_tok RUNTO HS HJ SHOK ArmBspan AR_CUT_EXIT; [apply awr_ok_x_nil |].
    pose proof (Hnw ms _ [] HFr ltac:(intros a (r & Hin & _); cbn [ss_mem] in Hin; destruct Hin)) as UN.
    pose proof (st_ok_pi_restrict_mkst (w_H W) _ _ _ HS eq_refl) as Ems. cbn [ss_pc] in Ems.
    destruct (arm_shape _ _ _ _ Ems) as (Sh1 & Sh2 & Sh3 & Sh4 & Sh5 & Sh6).
    apply (arm_exit_at ly S W msA mdA ms _ (-22) HA Sh1 Sh2 Sh3 Sh4 Sh5).
    - rewrite Sh6. reflexivity.
    - arm_rk_tac HS; rewrite R23, SN0; reflexivity.
    - prreg HS (10%bv : bv 5) Q10. rewrite Q10. apply bv_eq. reflexivity.
    - exact HJ.
    - exact (proj1 (wvb_fds_fs _ _ _)).
    - exact (proj2 (wvb_fds_fs _ _ _)).
    - intros a Ha. exact (apresent_grows _ _ _ a HG Ha).
    - exact UN.
    - intros nm Hnm. assert (nm = None) by exact (ar_astr_arg_unique SEGS _ _ _ _ Hnm SN0a). subst nm.
      rewrite ar_read_lib_none. reflexivity. }
  destruct SN0 as (Hn0 & HC).
  destruct (NMC sn eq_refl) as (Nfr & Ngn & Nlen & (Nmr & Nra & Nhv) & Ntl).
  pose proof (ar_acstr_range SEGS _ _ _ HC) as Rsn.
  assert (Hnb : forall x, AA 0 <= x < AA 0 + (Z.of_nat (length sn) + 1) -> RD x).
  { intros x Hx. left. split; [exact Hn0|]. exists sn. split; [exact HC | lia]. }
  (* the name at the stretch's memory, and its shadow *)
  assert (HCm : acstr_at SEGS (rdW W (ms_mem msA)) (AA 0) sn).
  { apply (ar_acstr_move SEGS (ar_m0 cx) _ _ _ HC). intros x Hx. unfold ar_m0.
    apply (YCbq.mbyte_of_aview SEGS). exact (HRK x (Hnb x ltac:(lia))). }
  destruct (ars_shadow_at SK B LAWS TB cx fpos HPRE HNIN HS1 tab kbs HNK HIT ly S W (ms_mem msA) mdA (AA 0)
    (Z.of_nat (length sn) + 1) HI0 ltac:(lia) (fun x Hx => sclass_of_akb SEGS B _ _ _ _ _ (HRD x (Hnb x Hx))) Nra Nhv)
    as (HRA & _).
  assert (SHOK : forall xs, sh_ok SEGS ArmBx [mkSHE 23 0 1] (armE (ms_regs msA) xs) (mrestrict (w_H W) (ms_mem msA))).
  { intros xs. constructor; [|constructor]. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
    rewrite EBx, E23. split.
    - intros x Hx. apply HRA. lia.
    - intros a Ha. cbn [Z.min Z.max] in Ha. unfold amem_range in Nmr. arx_c. unfold SHADOW_OFF. lia. }
  destruct sn as [|b0 s'].
  - (* the name is "": its check, `lbu` reads the NUL, `beqz a1` taken, a0 = -22 *)
    pose proof (armE_img (ms_regs msA) []) as HEI.
    assert (Hb0 : mbyte SEGS (rdW W (ms_mem msA)) (AA 0) = Some (zb 0)).
    { destruct HCm as ((_ & _ & Hby) & _). pose proof (Hby 0%nat ltac:(cbn; lia)) as H. rewrite Z.add_0_r in H.
      exact H. }
    assert (HS : st_ok_pi SEGS VAL (armE (ms_regs msA) []) (mkSS (AF_reac_link_alias_read + 0x150) sr_atoms
        [YP09.mkRegion (Some 23%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))]] None
        (mkFacts [(23%nat, mkAF 1 (2 ^ 47 - 1) 0); ArmF24] [] [])) (restrict (w_H W) msA)).
    { rewrite Hrms. apply pa_entry_st_ok_full; [apply armE_regs | vm_compute; reflexivity | | cbn; tauto |].
      - constructor; [|constructor]. unfold region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U23.
        split; [lia|]. split; [cbn [length Z.of_nat] in Rsn; lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS _ _ (AA 0) 0 1%N (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
        exact (arm_val1 _ _ _ Hb0).
      - split; [|split; exact I]. cbn [f_atoms atoms_ok ArmF24].
        split; [apply (arm_fact _ 23 _ _ _ (U23 [])); unfold amem_range in Nmr; arx_c; cbn [length Z.of_nat] in Nmr; lia|].
        split; [exact (F24 []) | exact I]. }
    pose proof (SHOK []) as SHOK0.
    paj_run_to_tok RUNTO HS HJ SHOK0 ArmBspan AR_CUT_EXIT.
    { intros a (r & Hin & Hw). cbn [In ss_mem] in Hin. destruct Hin as [<- | []].
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. lia. }
    pose proof (Hnw ms _ [] HFr ltac:(intros a (r & Hin & Hw); cbn [ss_mem In] in Hin; destruct Hin as [<- | []];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)) as UN.
    pose proof (st_ok_pi_restrict_mkst (w_H W) _ _ _ HS eq_refl) as Ems. cbn [ss_pc] in Ems.
    destruct (arm_shape _ _ _ _ Ems) as (Sh1 & Sh2 & Sh3 & Sh4 & Sh5 & Sh6).
    apply (arm_exit_at ly S W msA mdA ms _ (-22) HA Sh1 Sh2 Sh3 Sh4 Sh5).
    + rewrite Sh6. reflexivity.
    + arm_rk_tac HS.
    + prreg HS (10%bv : bv 5) Q10. rewrite Q10. apply bv_eq. reflexivity.
    + exact HJ.
    + exact (proj1 (wvb_fds_fs _ _ _)).
    + exact (proj2 (wvb_fds_fs _ _ _)).
    + intros a Ha. exact (apresent_grows _ _ _ a HG Ha).
    + exact UN.
    + intros nm Hnm. assert (nm = Some []) by exact (ar_astr_arg_unique SEGS _ _ _ _ Hnm SN0a). subst nm.
      rewrite ar_read_lib_empty. reflexivity.
  - (* the name is a non-empty C string: its check, its first byte, then fuzz_if_nametoindex(name) *)
    set (x0 := Z_to_bv 64 (bv_unsigned b0)).
    pose proof (armE_img (ms_regs msA) [x0]) as HEI.
    assert (Hb0 : mbyte SEGS (rdW W (ms_mem msA)) (AA 0) = Some b0).
    { destruct HCm as ((_ & _ & Hby) & _). pose proof (Hby 0%nat ltac:(cbn; lia)) as H. rewrite Z.add_0_r in H.
      exact H. }
    pose proof (bv_unsigned_in_range 8 b0) as Rb0. change (bv_modulus 8) with (2 ^ 8) in Rb0.
    assert (Hb0nz : bv_unsigned b0 <> 0).
    { intros H. apply (proj2 HC). left. apply bv_eq. rewrite H. reflexivity. }
    assert (U32 : bv_unsigned (ew (armE (ms_regs msA) [x0]) 32) = bv_unsigned b0).
    { rewrite armE_x32. unfold x0. apply unsigned_lit_small. lia. }
    assert (HS : st_ok_pi SEGS VAL (armE (ms_regs msA) [x0]) (mkSS (AF_reac_link_alias_read + 0x150) sr_atoms
        [YP09.mkRegion (Some 23%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))]] None
        (mkFacts [(23%nat, mkAF 1 (2 ^ 47 - 1) 0); ArmF24; (32%nat, mkAF 1 255 0)] [] [])) (restrict (w_H W) msA)).
    { rewrite Hrms. apply pa_entry_st_ok_full; [apply armE_regs | vm_compute; reflexivity | | cbn; tauto |].
      - constructor; [|constructor]. unfold region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U23.
        split; [lia|]. split; [cbn [length Z.of_nat] in Rsn; lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS _ _ (AA 0) 0 1%N (SOff 32 0) (bv_unsigned b0)); [| cbn; lia | cbn; lia |].
        + cbn [sv_denot]. rewrite U32, Z.add_0_r. reflexivity.
        + exact (arm_val1 _ _ _ Hb0).
      - split; [|split; exact I]. cbn [f_atoms atoms_ok ArmF24].
        split; [apply (arm_fact _ 23 _ _ _ (U23 [x0])); unfold amem_range in Nmr; arx_c; lia|].
        split; [exact (F24 [x0])|]. split; [apply (arm_fact _ 32 _ _ _ U32); lia | exact I]. }
    pose proof (SHOK [x0]) as SHOK0.
    pose (RUN := paj_run_x SK B LAWS (ar_G cx) HGx (ar_XO cx) (ar_OUT cx)).
    paj_run_tok RUN HS HJ SHOK0 ArmBspan.
    { intros a (r & Hin & Hw). cbn [In ss_mem] in Hin. destruct Hin as [<- | []].
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. lia. }
    pose proof (Hnw ms _ [x0] HFr ltac:(intros a (r & Hin & Hw); cbn [ss_mem In] in Hin; destruct Hin as [<- | []];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)) as UN1.
    pose proof (st_ok_restrict_mkst SEGS (w_H W) _ _ ms HS eq_refl) as Ems1. cbn [ss_pc setpc] in Ems1.
    prreg HS (1%bv : bv 5) Q1.
    prreg HS (10%bv : bv 5) Q10. rewrite (armE_reg _ _ 23 (23%bv : bv 5) eq_refl), R23 in Q10.
    assert (Hrk1 : arm_rk (ms_regs ms) (ms_regs msA)) by (arm_rk_tac HS).
    destruct Hrk1 as (G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
    lazymatch goal with |- SRr _ _ (mkCfg _ ?md) _ => set (md1 := md) end.
    assert (HI1 : ars_inv SK B cx fpos ly S W (ms_mem ms) md1).
    { apply (arm_inv_step ly S W (ms_mem msA) mdA (ms_mem ms) md1 (fun _ => False) HI0 HJ (fun a Ha _ => UN1 a Ha)
        (fun a Hx => match Hx with end) (fun a Ha => apresent_grows _ _ _ a HG Ha)); subst md1;
        [exact (proj1 (wvb_fds_fs _ _ _)) | exact (proj2 (wvb_fds_fs _ _ _))]. }
    pose proof HI1 as (HJ1 & Hfr1 & _ & Hperm1 & Hfa1 & _ & _ & _ & HK1 & _ & _ & HRO1).
    assert (HspN : spZ (ms_regs ms) = ar_sp1 cx).
    { unfold spZ. rewrite G2, R2b. apply unsigned_lit_small. lia. }
    assert (AN0 : aarg (ms_regs ms) 0 = AA 0).
    { apply (ars_aarg (ms_regs ms) 0 (10%bv : bv 5) (AA 0)); [apply bv_eq; reflexivity | exact Q10 | exact Rn0]. }
    assert (HGK1 : ar_gnl_kept cx W (ms_mem ms)).
    { intros a Ha. rewrite <- (HGK a Ha). apply UN1. arx_c. lia. }
    assert (HTL1 : ar_tails cx W (ms_mem ms)).
    { intros p str Hstr a Ha. exact (ar_vis_grows W _ _ a HG (HTL p str Hstr a Ha)). }
    assert (HCm1 : acstr_at SEGS (rdW W (ms_mem ms)) (AA 0) (b0 :: s')).
    { apply (ar_acstr_move SEGS _ _ _ _ HCm). intros x Hx. apply (YCbq.mbyte_of_aview SEGS). apply UN1. lia. }
    assert (HnE : forall a, ~ inFP (fuzz_if_nametoindex_awr (ms_regs ms) (rdW W (ms_mem ms))) a).
    { intros a (r & Hin & _). destruct Hin. }
    pose proof pa_B_ok as HBo. pose proof (pa_base_lo (PL := PL_link) (PI := PI)) as HBl.
    pose proof HAPRE as (_ & _ & _ & _ & _ & Hgp & Htp & _ & _ & _ & Hev & _).
    pose proof FUZZ_IF_NAMETOINDEX_AK_val as HFA.
    destruct (aj_stk_row_eq SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as [El Eh].
    destruct (aj_stk_row_eq SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ars_pre_j SK B cx HPRE)) as [Elc Ehc].
    (* ---- +0x174: fuzz_if_nametoindex(name) ---- *)
    rewrite Ems1.
    replace (pa_sigma LS_fuzz_if_nametoindex) with FUZZ_IF_NAMETOINDEX_A
      by (rewrite (lv_sigma HV); vm_compute; reflexivity).
    eapply SRr_bind.
    { apply (FIFN (ar_G cx) (ar_XO cx) (ar_OUT cx) (ar_STK cx) (ar_sp0 cx) (ar_FP cx) (ar_ly cx) (ar_S cx) (ar_W0 cx)
        (ar_mem0 cx) (ar_md0 cx) ((AR_CID, fpos) :: ar_own cx) ly S W (ms_mem ms) md1 (ar_k cx) (ms_regs ms)).
      - unfold apre, fuzz_if_nametoindex_awr.
        split; [exact HJ1|]. split; [exact HGx|]. split; [exact HRO1|].
        split; [rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]|].
        split; [unfold raZ; rewrite Q1, unsigned_lit_small by lia; lia|].
        split; [rewrite G3, R3b; exact Hgp|]. split; [rewrite G4, R4b; exact Htp|].
        split; [rewrite HspN; exact S1al|]. split; [rewrite HspN, HFA; lia|]. split; [rewrite HspN; lia|].
        split; [exact Hev|]. split; [constructor|].
        split; intros a (r & Hin & _); destruct Hin.
      - intros a (s2 & HC2 & Ha). rewrite AN0 in HC2, Ha.
        assert (s2 = b0 :: s') by exact (ar_acstr_unique SEGS _ _ _ _ HC2 HCm1). subst s2.
        rewrite HspN, HFA.
        apply (akb_sub SEGS B (ar_lyc cx) (ar_Sc cx) ly S (ar_sp cx - REAC_LINK_ALIAS_READ_AK) (ar_sp cx) _ _ a
          (HRD a (Hnb a ltac:(lia)))); [lia | lia | congruence | congruence
          | intros b' m' Hb; exact (Permutation_in _ (Permutation_sym Hperm1) Hb)
          | intros c q Hq; rewrite Hfr1; right; exact Hq | exact Hfa1].
      - unfold fuzz_if_nametoindex_apre. rewrite AN0. exists kbs, tab, (b0 :: s').
        split; [exact (arm_anlk_now W (ms_mem ms) HGK1)|].
        split; [exact (arx_tab_kept SK B LAWS TB HSEGS cx fpos HPRE HNIN HS1 kbs tab W (ms_mem ms) kbs HNK HIT HK1 eq_refl)|].
        destruct (ars_shadow_at SK B LAWS TB cx fpos HPRE HNIN HS1 tab kbs HNK HIT ly S W (ms_mem ms) md1 LA_G_NL NK_SIZE
          HI1 ltac:(arx_c; lia)
          (fun x Hx => or_intror (or_intror (or_introl (proj1 (arx_gnl_img B TB HSEGS x Hx))))) RA0 HV0) as [RAg _].
        pose proof HIT as (Ln & L80 & EIT).
        split; [intros x Hx; apply RAg; arx_c; lia|].
        split; [intros x Hx; apply RAg; arx_c; lia|].
        split; [exact Hn0|]. split; [exact HCm1|].
        split.
        { destruct (ars_shadow_at SK B LAWS TB cx fpos HPRE HNIN HS1 tab kbs HNK HIT ly S W (ms_mem ms) md1 (AA 0)
            (Z.of_nat (length (b0 :: s')) + 1) HI1 ltac:(lia)
            (fun x Hx => sclass_of_akb SEGS B _ _ _ _ _ (HRD x (Hnb x Hx))) Nra Nhv) as [RAn HVn].
          split; [lia|]. split; [exact Nlen|]. split; [exact Nmr|]. split; [exact RAn|]. split; [exact HVn|].
          split;
          [ unfold apart_frame in *; rewrite HspN, HFA;
            change (spZ (ar_regs cx)) with (ar_sp cx) in Nfr; lia |].
          intros a Ha.
          exact (HTL1 (AA 0) (b0 :: s')
            ltac:(unfold ar_tail_str; left; split; [reflexivity | split; [exact Hn0 | exact HC]]) a Ha). }
        intros i n2 ix p Hi Hp Hp64.
        destruct (EIT i n2 ix Hi) as (Rx & p' & U' & Hp0 & C' & I').
        assert (Hil : (i < length tab)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
        assert (U'1 : au64_at SEGS (rdW W (ms_mem ms)) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p').
        { intros k Hk. rewrite <- (U' k Hk). unfold ar_m0. apply (YCbq.mbyte_of_aview SEGS). apply HGK1.
          arx_c. lia. }
        pose proof (ar_au64_unique SEGS _ _ _ _ Hp U'1) as Ep. pose proof (ar_acstr_range SEGS _ _ _ C') as Rp.
        rewrite !Z.mod_small in Ep by lia. subst p'.
        destruct (TABC i n2 ix p Hi U') as (Tfr & _ & _ & _ & _ & POS).
        destruct (POS ltac:(lia)) as (Pp & Pl & (Pmr & Pra & Phv) & Ptl).
        assert (Htb : forall x, p <= x < p + (Z.of_nat (length n2) + 1) -> RD x).
        { intros x Hx. right. exists kbs, tab, i, n2, ix, p.
          split; [exact HNK|]. split; [exact HIT|]. split; [exact Hi|]. split; [exact U'|]. split; [exact C'|]. lia. }
        destruct (ars_shadow_at SK B LAWS TB cx fpos HPRE HNIN HS1 tab kbs HNK HIT ly S W (ms_mem ms) md1 p
          (Z.of_nat (length n2) + 1) HI1 ltac:(lia)
          (fun x Hx => sclass_of_akb SEGS B _ _ _ _ _ (HRD x (Htb x Hx))) Pra Phv) as [RAp HVp].
        split; [exact Pp|]. split; [exact Pl|]. split; [exact Pmr|]. split; [exact RAp|]. split; [exact HVp|].
        split;
        [ unfold apart_frame in *; rewrite HspN, HFA;
          change (spZ (ar_regs cx)) with (ar_sp cx) in Tfr; lia |].
        intros a Ha.
        exact (HTL1 p n2
          ltac:(unfold ar_tail_str; right; exists kbs, tab, i, ix;
                split; [exact HNK | split; [exact HIT | split; [exact Hi | split; [exact U' |
                split; [exact Hp64 | exact C']]]]])
          a Ha). }
    cbv beta. intros W2 c2 _ HQ.
    destruct HQ as (ly2 & S2 & regs2 & mem2 & md2 & Ec2 & HJ2 & HP2 & Hfr2 & Hfds2 & Hfs2 & HK2 & _ & HS2 & Hperm2 & HPOST).
    subst c2. rewrite Z.add_0_r in HJ2.
    (* ---- +0x178: the return ---- *)
    pose proof (ars_nl_step SK B LAWS HSEGS cx fpos HPRE HNIN HS1 tab kbs HNK HIT ly S W (ms_mem ms) md1 ly2 S2 W2 mem2
      md2 _ _ _ HI1 HJ2 Hfr2 HS2 Hperm2 Hfds2 Hfs2 HK2 ltac:(rewrite HspN, HFA; lia) ltac:(rewrite HspN; lia)
      (fun a Ha => match HnE a Ha with end)) as HI2.
    assert (P : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs ms) r).
    { intros r Hr. exact (ars_pres _ _ r _ HP2 Hr eq_refl). }
    assert (HGK2 : ar_gnl_kept cx W2 mem2).
    { intros a Ha. pose proof HK2 as (_ & _ & K3 & _).
      destruct (arx_gnl_img B TB HSEGS a Ha) as (I1 & I2 & I3).
      rewrite (K3 a I1 I2 I3 (HnE a)). exact (HGK1 a Ha). }
    assert (HKB : forall i j a, arm_buf i j -> AA i <> 0 -> 1 <= AA j -> AA i <= a < AA i + AA j ->
      aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) (ms_mem ms) a).
    { intros i j a Hij H0 H1 Ha.
      destruct (arm_pre_buf i j Hij H0 H1) as (_ & _ & Hf & _ & Her).
      eapply (akept_akb_gx SK SEGS B); [exact HJ1 | exact HK2 | | exact (HnE a)].
      eapply (ajw_akb SK SEGS B LAWS);
        [exact HGx | exact (ars_pre_j SK B cx HPRE) | exact (ars_pre_ajw SK B cx HPRE a (arm_buf_E i j a Hij H0 Ha))
        | | exact (ars_E_app SK B cx HPRE tab kbs HNK HIT a (arm_buf_E i j a Hij H0 Ha)) | unfold apart in Her; lia
        | congruence | congruence | intros b' m' Hb; exact (Permutation_in _ (Permutation_sym Hperm1) Hb)
        | intros c q Hq; rewrite Hfr1; right; exact Hq | exact Hfa1].
      rewrite HspN, HFA. unfold apart_frame in Hf. change (spZ (ar_regs cx)) with (ar_sp cx) in Hf. lia. }
    assert (HBN2 : ar_bufs_nul cx W2 mem2).
    { split.
      - apply (bdone_move 1 2 W W2 (ms_mem ms) mem2 (or_introl (conj eq_refl eq_refl))
          (fun a H0 H1 Ha => HKB 1 2 a (or_introl (conj eq_refl eq_refl)) H0 H1 Ha)).
        exact (bdone_keep 1 2 W (ms_mem msA) (ms_mem ms) (or_introl (conj eq_refl eq_refl))
          (fun a H0 H1 Ha => UN1 a (arm_buf_rng 1 2 a (or_introl (conj eq_refl eq_refl)) H0 Ha)) HKD).
      - apply (bdone_move 3 4 W W2 (ms_mem ms) mem2 (or_intror (conj eq_refl eq_refl))
          (fun a H0 H1 Ha => HKB 3 4 a (or_intror (conj eq_refl eq_refl)) H0 H1 Ha)).
        exact (bdone_keep 3 4 W (ms_mem msA) (ms_mem ms) (or_intror (conj eq_refl eq_refl))
          (fun a H0 H1 Ha => UN1 a (arm_buf_rng 3 4 a (or_intror (conj eq_refl eq_refl)) H0 Ha)) HAD). }
    assert (E10 : getr regs2 10 = w64 (index_of tab (b0 :: s'))).
    { apply (HPOST kbs tab (b0 :: s')); [exact (arm_anlk_now W (ms_mem ms) HGK1)
      | exact (arx_tab_kept SK B LAWS TB HSEGS cx fpos HPRE HNIN HS1 kbs tab W (ms_mem ms) kbs HNK HIT HK1 eq_refl)
      | rewrite AN0; exact HCm1]. }
    rewrite Q1.
    apply (arm_after_call ly2 S2 W2 regs2 mem2 md2 (b0 :: s') HI2).
    + rewrite (P (2%bv : bv 5) ltac:(arm_cs)), G2. exact R2b.
    + rewrite (P (9%bv : bv 5) ltac:(arm_cs)), G9. exact R9b.
    + rewrite (P (8%bv : bv 5) ltac:(arm_cs)), G8. exact R8b.
    + rewrite (P (18%bv : bv 5) ltac:(arm_cs)), G18. exact R18b.
    + rewrite (P (26%bv : bv 5) ltac:(arm_cs)), G26. exact R26b.
    + rewrite (P (25%bv : bv 5) ltac:(arm_cs)), G25. exact R25b.
    + rewrite (P (3%bv : bv 5) ltac:(arm_cs)), G3. exact R3b.
    + rewrite (P (4%bv : bv 5) ltac:(arm_cs)), G4. exact R4b.
    + rewrite (P (27%bv : bv 5) ltac:(arm_cs)), G27. exact R27b.
    + rewrite (P (19%bv : bv 5) ltac:(arm_cs)), G19. exact R19.
    + rewrite (P (20%bv : bv 5) ltac:(arm_cs)), G20. exact R20.
    + rewrite (P (21%bv : bv 5) ltac:(arm_cs)), G21. exact R21.
    + rewrite (P (22%bv : bv 5) ltac:(arm_cs)), G22. exact R22.
    + rewrite (P (24%bv : bv 5) ltac:(arm_cs)), G24. exact R24.
    + exact E10.
    + exact HGK2.
    + exact HBN2.
    + exact HC.
    + exact Hn0.
    + discriminate.
Qed.

End c.
(* ==========================================================================
   5. THE ARMS
   ========================================================================== *)
Theorem ar_arms : ar_send_obl SK B -> ar_exit_obl SK B -> ar_mid_obl SK B.
Proof.
  intros SENDO EXIT cx fpos ly3 S3 W3 ms3 md3 HPRE
    (Hpc & R19 & R20 & R21 & R22 & R23 & R24 & HGK & HRK & HTL & (HKK & HAK) & HB).
  pose proof HB as HB0. unfold ar_base in HB0. cbv zeta in HB0.
  destruct HB0 as (_ & _ & _ & _ & _ & _ & _ & Hnin & _ & _ & (S1 & W1 & mem1 & md1 & HAR1 & Hfrs1 & Eab1) & _).
  assert (HS1 : exists S1 W1 mem1 md1, AR SEGS B (ar_lyc cx) S1 W1 mem1 md1 /\
    frames S1 = (AR_CID, fpos) :: frames (ar_Sc cx) /\ ablocks B (ar_lyc cx) S1 = ablocks B (ar_lyc cx) (ar_Sc cx))
    by (exists S1, W1, mem1, md1; exact (conj HAR1 (conj Hfrs1 Eab1))).
  pose proof HPRE as (_ & _ & (kbs & tab & nm & NK & _ & _ & _ & _ & IT & _)).
  apply (arm_kind cx fpos HPRE Hnin HS1 tab kbs NK IT ly3 S3 W3 ms3 md3).
  - exact (conj Hpc (conj R19 (conj R20 (conj R21 (conj R22 (conj R23 (conj R24 (conj HGK (conj HRK (conj HKK (conj HAK (conj HTL HB)))))))))))).
  - intros ms4 md4 H4. apply (arm_alias cx fpos HPRE Hnin HS1 tab kbs NK IT ly3 S3 W3 ms4 md4 H4).
    intros ms5 md5 H5. exact (arm_tail cx fpos HPRE Hnin HS1 tab kbs NK IT EXIT SENDO ly3 S3 W3 ms5 md5 H5).
Qed.

End b.
End a.

Arguments ar_arms {fx rc} SK {PI}.
About ar_arms.
Print Assumptions ar_arms.
