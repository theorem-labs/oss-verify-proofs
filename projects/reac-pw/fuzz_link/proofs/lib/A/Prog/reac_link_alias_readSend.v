(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a segment of reac_headamp_tx_next on fuzz_grant.asan (NextEntry), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/NextEntry.v at a working branch af735a950e2 (blob 8725db69d2a; the walk was ported from blob 7788bf8f6e4 at a working branch afd75724b5b, which differs from it only by 4 added and 0 removed lines, the licence header), restated over image B's listing, addresses and walk layer (lib/B/Prog) against GrantBContracts.v; frame 96 with twelve saved registers, UBSan traps T1 and T2, and the .rodata divisor read at 0x85fa4 (IMG_NEXT_DIV3) *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/NextEntry.v, with its module paths and module names changed; 542 of its 591 lines of code are new or changed and 711 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_link_alias_readExit.v; 1071 of its 1182 lines of code are new or changed and 480 lines of the source are left out. *)
(* reac_link_alias_read (fuzz_link.asan 0x8867c, listing offset AF_reac_link_alias_read) on image A, THE SEND PIECE:
   from the SEND cut (+0x180, `addi s8,s10,0x20`) to the EXIT cut (+0x1fc). It proves reac_link_alias_readDefs.v's
   obligation `ar_send_obl` from `ar_exit_obl`.

   The walk (listing (internal path) (internal record, sha256 7c23ed8f465f)):
     +0x180..+0x1a0  s8 := q = F + 32, the request's four shadow bytes SH + 4 .. SH + 7 := 0: a plain run to the
                     call of checked_memset (0x53214)
     +0x1a0          checked_memset(q + 12, 0, 20): link_ajkit.v aj_gx_intrin_at, op OSet
     +0x1a4..+0x1dc  the four header words of the request (32, 65554, 1, the index); a plain run to the call of
                     nl_talk (0x88974)
     +0x1dc          nl_talk(q, 32, kind, kind_n, alias, alias_n): nl_talk_c.v nl_talk_acontract under SRr_bind
     +0x1e0..+0x1f4  the request's shadow := 0xf8 again; a plain run to the EXIT cut, handed to ar_exit_obl
   Each stage starts a fresh symbolic state whose atoms are the stage's registers (sr_atoms), as
   reac_link_alias_write's SEND piece does; the stages share the memory facts the walk carries (`ars_inv`: ar_base
   without the registers and the machine state's shape).

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkPi LinkWalkSide LinkWalkZsh LinkWalkShadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkCall.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_link_alias_read_c nl_talk_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_link_alias_readDefs reac_link_alias_readPost.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_link_alias_readExit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AF0m AB1v.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number -notation-for-abbreviation".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* No global sink_head instance is in scope: every journal below is the Section's SK. *)
Fail Definition sink_head_probe_ars : YI16.sink_head := _.

(* ---- the symbolic states of the three stages: registers as atoms ---- *)
(* the frame's shadow (s9, atom 25); the stores of +0x184..+0x190 and +0x1e4..+0x1f0 reach SH + 4 .. SH + 7 *)
Definition ars_sh_r : YP09.region := YP09.mkRegion (Some 25%nat) 0 16 4 8 [].
(* the request q (s8, atom 24): the three header words at q + 0 .. q + 12 and the index at q + 20 .. q + 24; the
   bytes checked_memset zeroed (q + 12 .. q + 20, q + 24 .. q + 32) lie outside both windows *)
Definition ars_reqa_r : YP09.region := YP09.mkRegion (Some 24%nat) 0 12 0 12 [].
Definition ars_reqb_r : YP09.region := YP09.mkRegion (Some 24%nat) 20 24 20 24 [].
Definition ars_ss1 : sstate := mkSS AR_CUT_SEND sr_atoms [ars_sh_r] None (mkFacts [] [] []).
Definition ars_ss2 : sstate :=
  mkSS (AF_reac_link_alias_read + 0x1a4) sr_atoms [ars_reqa_r; ars_reqb_r] None (mkFacts [] [] []).
Definition ars_ss3 : sstate := mkSS (AF_reac_link_alias_read + 0x1e0) sr_atoms [ars_sh_r] None (mkFacts [] [] []).

(* a plain run of the walk's own code on the caller's journal, its end state computed; the listing tree is read
   off the lemma's own type *)
Ltac ars_run_to RUNT HS HJ stop :=
  let T := type of RUNT in
  lazymatch T with context [sym_run_toN_pi ?tpi _ _ _] =>
  lazymatch type of HS with
  | st_ok_pi _ _ ?E ?ss (restrict (w_H ?W) ?ms) =>
    let r := eval vm_compute in (sym_run_toN_pi tpi FUEL stop ss) in
    lazymatch r with
    | (?ss', ?st) =>
      let Hrun := fresh "Hrun" in
      assert (Hrun : sym_run_toN_pi tpi FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
      let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI end in
      eapply (RUNT W FUEL stop E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun I HJ);
      clear Hrun
    end
  end end.
Ltac ars_run_call RUNC HS HJ :=
  let T := type of RUNC in
  lazymatch T with context [sym_runN_pi ?tpi _ _] =>
  lazymatch type of HS with
  | st_ok_pi _ _ ?E ?ss (restrict (w_H ?W) ?ms) =>
    let r := eval vm_compute in (sym_runN_pi tpi FUEL ss) in
    lazymatch r with
    | (?ss', PRS_call ?s) =>
      let Hrun := fresh "Hrun" in
      assert (Hrun : sym_runN_pi tpi FUEL ss = (ss', PRS_call s)) by (vm_compute; reflexivity);
      let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI end in
      eapply (RUNC W FUEL E ss ss' s ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun HJ);
      clear Hrun
    end
  end end.
(* a chunk of a computed region list *)
Ltac ars_in := repeat (first [left; reflexivity | right]).

Lemma ars_toa_len : forall o c, 1 <= c -> Z.of_nat (length (text_of_attr o c)) <= c - 1.
Proof. intros [pay|] c Hc; [apply cut_text_len; exact Hc | cbn [text_of_attr length]; lia]. Qed.

Lemma ars_rdword_eq : forall (rd rd' : reader) a,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
  intros rd rd' a H.
  assert (E0 : rd' a = rd a) by (specialize (H 0 ltac:(lia)); rewrite Z.add_0_r in H; exact H).
  unfold rdword. rewrite E0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

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
(* the image instance: AR's laws, the listing's values (nl_talk's entry), the start-up symbols (the runtime's statics
   and errno), and the image's segments (g_nl and errno writable, the relro window in the image: computations) *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HV : LinkVals.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : SEGS = tfibsegs.
(* checked_memset (0x53214): lib/A/AE2r.v asan_memset_realizes at tfibsegs, whose premise order differs from
   aintrin_realizes only by moving `amem_range d n` after the two shadow premises *)
Hypothesis AMSET : aintrin_realizes SEGS B OSet (pa_sigma LS___asan_memset).
(* nl_talk (0x88974): lib/A/Prog/nl_talk.v nl_talk_aproof *)
Hypothesis NLT : nl_talk_acontract SK SEGS PCAP_RLO PCAP_RHI B.

(* ---- byte views ---- *)
Lemma ars_writable_grow : forall (H : word -> bool) (m m' : word -> option byte) a,
  writable_at SEGS (mrestrict H m) a -> (apresent H m a -> apresent H m' a) -> writable_at SEGS (mrestrict H m') a.
Proof.
  intros H m m' a Hw Hp. unfold writable_at, wview, mrestrict, apresent in *. cbv beta in *.
  revert Hw Hp. destruct (H (Z_to_bv 64 a)); intros Hw Hp; [exact Hw|].
  revert Hw Hp. destruct (m (Z_to_bv 64 a)) as [b|]; intros Hw Hp.
  - destruct (Hp (conj eq_refl (ex_intro _ b eq_refl))) as [_ [b' Hb']]. rewrite Hb'. cbv beta iota. discriminate.
  - destruct (m' (Z_to_bv 64 a)) as [b'|]; [cbv beta iota; discriminate | exact Hw].
Qed.

Lemma ars_aview0 : forall (H : word -> bool) (m : word -> option byte) a,
  aview SEGS H m a = Some 0 -> mbyte SEGS (mrestrict H m) a = Some (Z_to_bv 8 0).
Proof.
  intros H m a Hv. unfold aview in Hv. revert Hv.
  destruct (mbyte SEGS (mrestrict H m) a) as [b|]; cbn [option_map]; intros Hv; [|discriminate].
  injection Hv as Hv. f_equal. apply bv_eq. rewrite Hv. reflexivity.
Qed.

Lemma ars_mbyte0_aview : forall (H : word -> bool) (m : word -> option byte) a,
  mbyte SEGS (mrestrict H m) a = Some (Z_to_bv 8 0) -> aview SEGS H m a = Some 0.
Proof. intros H m a Hm. unfold aview. rewrite Hm. reflexivity. Qed.

Lemma ars_ms_eta : forall ms : machine_state, ms_resv ms = None -> ms_svc_pending ms = None ->
  ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr -> ms = mkst (ms_regs ms) (ms_pc_val ms) (ms_mem ms) (ms_rom ms).
Proof. intros [] H1 H2 H3 H4. cbn in *. subst. reflexivity. Qed.

Lemma ars_present_vis : forall (H : word -> bool) (m : word -> option byte) a,
  apresent H m a -> aview SEGS H m a <> None.
Proof.
  intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. cbv beta. rewrite Hh, Hb. cbn [option_map]. discriminate.
Qed.

Lemma ars_frame_aview : forall E rs (H : word -> bool) (m m' : word -> option byte) x,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= x < 2 ^ 64 -> ~ in_wrange E rs x ->
  aview SEGS H m' x = aview SEGS H m x.
Proof.
  intros E rs H m m' x HF Hx Hn. apply (YCbq.aview_eq_of SEGS). apply HF. rewrite unsigned_lit_small by lia. exact Hn.
Qed.

Lemma ars_anlk_vkeep : forall (W : world SEGS) m m' bs, anlk_at SEGS (rdW W m) LA_G_NL bs ->
  (forall x, LA_G_NL <= x < LA_G_NL + NK_SIZE -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  anlk_at SEGS (rdW W m') LA_G_NL bs.
Proof.
  intros W m m' bs HN Hk. apply (ar_anlk_move SEGS _ _ bs HN); intros x Hx.
  - apply (YCbq.mbyte_of_aview SEGS). exact (Hk x Hx).
  - pose proof (LA_G_NL_writable (rdW W m') x ltac:(unfold NK_SIZE in Hx; lia)) as Hw.
    rewrite <- HSEGS in Hw. exact Hw.
Qed.

Lemma ars_acstr_vkeep : forall (W : world SEGS) m m' p s, acstr_at SEGS (rdW W m) p s ->
  (forall x, p <= x <= p + Z.of_nat (length s) -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  acstr_at SEGS (rdW W m') p s.
Proof.
  intros W m m' p s HC Hk. apply (ar_acstr_move SEGS _ _ p s HC). intros x Hx.
  apply (YCbq.mbyte_of_aview SEGS). exact (Hk x Hx).
Qed.

Lemma ars_abuf_vkeep : forall (W : world SEGS) m m' p n, abuf SEGS (rdW W m) p n ->
  (forall x, p <= x < p + n -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  (forall x, p <= x < p + n -> apresent (w_H W) m x -> apresent (w_H W) m' x) ->
  abuf SEGS (rdW W m') p n.
Proof.
  intros W m m' p n HB Hk Hp. pose proof HB as (junk & L & _ & Hw). unfold awrange in Hw.
  apply (ar_abuf_move SEGS _ _ p n HB); intros x Hx.
  - apply (YCbq.mbyte_of_aview SEGS). exact (Hk x Hx).
  - apply (ars_writable_grow _ m); [|exact (Hp x Hx)].
    replace x with (p + (x - p)) by lia. apply Hw. lia.
Qed.

Lemma ars_arodata_eq : forall rlo rhi (rd rd' : reader),
  arodata_okP SEGS rlo rhi B rd -> (forall a, in_roP SEGS rlo rhi a -> rd' a = rd a) ->
  arodata_okP SEGS rlo rhi B rd'.
Proof. intros rlo rhi rd rd' H Hk a Hro Ho He. rewrite (Hk a Hro). exact (H a Hro Ho He). Qed.

(* the relro window and the read-only segments are image bytes (a computation at the image's segments) *)
Lemma ars_ro_img : forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> in_img SEGS a.
Proof.
  intros a [(s & Hs & _ & Hb) | Hr]; [exists s; split; [exact Hs | exact Hb]|].
  rewrite HSEGS.
  assert (Hb : existsb (fun sg => (Z.of_N (seg_base sg) <=? PCAP_RLO) &&
      (PCAP_RHI <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) tfibsegs = true) by (vm_compute; reflexivity).
  apply existsb_exists in Hb as (sg & Hin & Hc). apply andb_true_iff in Hc as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. exists sg. split; [exact Hin | lia].
Qed.

(* errno: an image byte, writable at every memory (a computation at the image's segments) *)
Lemma ars_errno_val : as_errno B = 0x631b6c.
Proof. rewrite (ts_errno B TB). reflexivity. Qed.

Lemma ars_wseg_errno : YK1d.wseg_ok tfibsegs (Z_to_bv 64 0x631b6c) (Z.to_nat 4) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ars_errno_writable : forall m a, as_errno B <= a < as_errno B + 4 -> writable_at SEGS m a.
Proof.
  rewrite ars_errno_val, HSEGS. intros m.
  apply writable_at_of_wseg; [lia | lia | exact ars_wseg_errno].
Qed.

Lemma ars_errno_img : forall a, as_errno B <= a < as_errno B + 4 -> in_img SEGS a.
Proof.
  rewrite ars_errno_val, HSEGS. intros a Ha.
  assert (Hb : existsb (fun sg => (Z.of_N (seg_base sg) <=? 0x631b6c) &&
      (0x631b6c + 4 <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) tfibsegs = true) by (vm_compute; reflexivity).
  apply existsb_exists in Hb as (sg & Hin & Hc). apply andb_true_iff in Hc as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. exists sg. split; [exact Hin | lia].
Qed.

(* the denotation of a register atom of a stage's environment *)
Lemma ars_atom : forall (R : bvmap 5 word) (n : nat) (r : bv 5),
  Z.of_nat n = bv_unsigned r -> sv_denot (Eimg (Ereg R [])) (SOff n 0) = getr R r.
Proof.
  intros R n r H. cbn [sv_denot]. rewrite (ew_Eimg_Ereg_nat R [] n r H). rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  reflexivity.
Qed.

Lemma ars_atom_off : forall (R : bvmap 5 word) (n : nat) (r : bv 5) v k,
  Z.of_nat n = bv_unsigned r -> getr R r = w64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot (Eimg (Ereg R [])) (SOff n k) = w64 (v + k).
Proof.
  intros R n r v k H Hv Hr. cbn [sv_denot]. rewrite (ew_Eimg_Ereg_nat R [] n r H), Hv. unfold w64.
  rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Lemma ars_U : forall (R : bvmap 5 word) (n : nat) (r : bv 5) v,
  Z.of_nat n = bv_unsigned r -> getr R r = w64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew (Eimg (Ereg R [])) n) = v.
Proof. intros R n r v H Hv Hr. rewrite (ew_Eimg_Ereg_nat R [] n r H), Hv. apply unsigned_lit_small. lia. Qed.

Lemma ars_aarg : forall (R : bvmap 5 word) i (r : bv 5) v,
  Z_to_bv 5 (10 + i) = r -> getr R r = w64 v -> 0 <= v < 2 ^ 64 -> aarg R i = v.
Proof. intros R i r v H Hv Hr. unfold aarg, argZ. rewrite H, Hv. apply unsigned_lit_small. lia. Qed.

Lemma ars_aarg_rng : forall (R : bvmap 5 word) i, 0 <= aarg R i < 2 ^ 64.
Proof.
  intros R i. unfold aarg, argZ. pose proof (bv_unsigned_in_range 64 (getr R (Z_to_bv 5 (10 + i)))) as Q.
  change (bv_modulus 64) with (2 ^ 64) in Q. exact Q.
Qed.

(* a register's value through an own call's aregs_preserved *)
Lemma ars_pres : forall (R R2 : bvmap 5 word) (r : bv 5) v, aregs_preserved R R2 -> acallee_saved (bv_unsigned r) ->
  getr R r = v -> getr R2 r = v.
Proof.
  intros R R2 r v P Hr H. pose proof (P (bv_unsigned r) Hr) as Q. rewrite !Z_to_bv_bv_unsigned in Q.
  rewrite Q. exact H.
Qed.

Ltac ars_cs := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?r] =>
    let v := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with v end; lia.

(* ==========================================================================
   1. The call's context and the invariant every stage carries
   ========================================================================== *)
Section c.
Variable cx : arcx.
Variable fpos : Z.
#[local] Notation F := (ar_F cx fpos).
#[local] Notation SH := (ar_SH cx fpos).
#[local] Notation FL := (ar_FL cx fpos).
#[local] Notation AK := REAC_LINK_ALIAS_READ_AK.
#[local] Notation Eacc := (fun a => ar_E cx a \/ aside_rng (ar_lyc cx) AR_CID fpos a).
#[local] Notation AJ ly S W m md :=
  (ajournal_gx SEGS B (ar_G cx) (ar_XO cx) (ar_OUT cx) (ar_STK cx) (ar_sp0 cx) (ar_FP cx)
     (ar_ly cx) (ar_S cx) (ar_W0 cx) (ar_mem0 cx) (ar_md0 cx) ((AR_CID, fpos) :: ar_own cx) ly S W m md (ar_k cx)).

Hypothesis HPRE : ar_pre SK B cx.
Hypothesis HNIN : ~ In (AR_CID, fpos) (frames (ar_Sc cx)).
Hypothesis HS1 : exists S1 W1 mem1 md1, AR SEGS B (ar_lyc cx) S1 W1 mem1 md1 /\
  frames S1 = (AR_CID, fpos) :: frames (ar_Sc cx) /\ ablocks B (ar_lyc cx) S1 = ablocks B (ar_lyc cx) (ar_Sc cx).
(* the cut's name, table and kernel bytes (ar_gi_send), at the call's memory *)
Variables (sn : list byte) (tab : list (list byte * Z)) (kbs : list byte).
Hypothesis HNK : anlk_at SEGS (ar_m0 cx) LA_G_NL kbs.
Hypothesis HIT : aiftab_at SEGS (ar_m0 cx) LA_G_NL kbs tab.
Hypothesis HSN : acstr_at SEGS (ar_m0 cx) (ar_name cx) sn.
Hypothesis HN0 : ar_name cx <> 0.
Hypothesis HSNE : sn <> [].
Hypothesis HIDX : index_of tab sn <> 0.
(* the EXIT piece (lib/A/Prog/reac_link_alias_readExit.v ar_exit) *)
Hypothesis EXIT : ar_exit_obl SK B.
#[local] Notation K0 := (nk_kstate kbs).
#[local] Notation IDX := (index_of tab sn).

Lemma ars_pre_j : ajournal_gx SEGS B (ar_G cx) (ar_XO cx) (ar_OUT cx) (ar_STK cx) (ar_sp0 cx) (ar_FP cx)
  (ar_ly cx) (ar_S cx) (ar_W0 cx) (ar_mem0 cx) (ar_md0 cx) (ar_own cx)
  (ar_lyc cx) (ar_Sc cx) (ar_W cx) (ar_memc cx) (ar_mdc cx) (ar_k cx).
Proof. exact (proj1 (proj1 HPRE)). Qed.

Lemma ars_pre_g : gx_ok SEGS B (ar_G cx).
Proof. exact (proj1 (proj2 (proj1 HPRE))). Qed.

Lemma ars_pre_ar : AR SEGS B (ar_lyc cx) (ar_Sc cx) (ar_W cx) (ar_memc cx) (ar_mdc cx).
Proof. exact (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ars_pre_j). Qed.

Lemma ars_win : ar_sp cx mod 16 = 0 /\ alloc_ceiling <= ar_sp0 cx - ar_STK cx /\
  ar_sp0 cx - ar_STK cx <= ar_sp cx - AK /\ ar_sp cx <= ar_sp0 cx /\ ar_sp0 cx <= 2 ^ 47 /\
  ar_sp cx - 144 <= ar_sp1 cx <= ar_sp cx - 128 /\ ar_sp1 cx mod 16 = 0.
Proof.
  destruct HPRE as ((HJ & _ & _ & _ & _ & _ & _ & H16 & Hlo & Hhi & _) & _ & _).
  destruct HJ as (HSTK & HXO & (memS & HJi & _) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as ((C1a & C1b) & _). pose proof REAC_LINK_ALIAS_READ_AK_val as HK8.
  fold (ar_sp cx) in H16, Hlo, Hhi.
  destruct (sp1_facts (ar_sp cx - 128) ltac:(lia) ltac:(rewrite Zminus_mod, H16; reflexivity)) as (S1 & S2 & S3).
  unfold ar_sp1, AR_FRAME. repeat split; lia.
Qed.

Lemma ars_F : 4096 <= F /\ F + 128 <= alloc_ceiling /\ F mod 64 = 0 /\ in_app F 128 /\ off_img F 128 /\
  0 <= fpos < fs_frames AR_CID.
Proof. exact (arx_F B LAWS cx fpos HS1). Qed.

Lemma ars_SH : SH = SHADOW_OFF + F / 8 /\ SH mod 8 = 0 /\ 0x7fff8000 + 512 <= SH /\ SH <= 0x7fff8000 + 2 ^ 44 /\
  SH + 16 <= alloc_ceiling /\ (F + 128 <= SH \/ SH + 16 <= F).
Proof. exact (arx_SH B LAWS cx fpos HS1). Qed.

(* the facts of the contract's Pre the stages read, at the call's memory *)
Lemma ars_pre_ajw : forall a, inFP (ar_wr cx) a ->
  ajw B (ar_G cx) (ar_XO cx) (ar_OUT cx) (ar_STK cx) (ar_sp0 cx) (ar_FP cx) (ar_ly cx) (ar_S cx)
    (ar_lyc cx) (ar_Sc cx) (ar_own cx) a.
Proof. destruct HPRE as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _) & _). exact H. Qed.

Lemma ars_pre_nro : forall a, inFP (ar_wr cx) a -> ~ in_roP SEGS PCAP_RLO PCAP_RHI a.
Proof. destruct HPRE as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H) & _). exact H. Qed.

Lemma ars_pre_bufs :
  (aarg (ar_regs cx) 1 <> 0 -> apart_frame (ar_regs cx) AK (aarg (ar_regs cx) 1) (aarg (ar_regs cx) 2)
     /\ apart_gnl LA_G_NL (aarg (ar_regs cx) 1) (aarg (ar_regs cx) 2)) /\
  (aarg (ar_regs cx) 3 <> 0 -> apart_frame (ar_regs cx) AK (aarg (ar_regs cx) 3) (aarg (ar_regs cx) 4)
     /\ apart_gnl LA_G_NL (aarg (ar_regs cx) 3) (aarg (ar_regs cx) 4)).
Proof.
  destruct HPRE as (_ & _ & (kbs0 & tab0 & nm0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & KF & AF & _ & _)).
  split; assumption.
Qed.

(* the write set's bytes are application bytes (they miss every frame's shadow) *)
Lemma ars_E_app : forall a, ar_E cx a -> a < kLowMemEnd \/ kHighMemBeg <= a.
Proof.
  intros a HE.
  destruct HPRE as (_ & _ & (kbs0 & tab0 & nm0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & KCH & ACH)).
  apply (arx_E_iff cx) in HE. destruct HE as [HE | [(H0 & HE) | (H0 & HE)]].
  - arx_c. left. lia.
  - destruct (KCH H0 ltac:(lia)) as (Hr & _). unfold amem_range in Hr. lia.
  - destruct (ACH H0 ltac:(lia)) as (Hr & _). unfold amem_range in Hr. lia.
Qed.

Lemma ars_fmiss : fmiss (ar_lyc cx) (ar_Sc cx) Eacc.
Proof.
  destruct ars_F as (_ & _ & _ & _ & _ & Hfp).
  apply fmiss_or.
  - exact (fmiss_app SEGS B LAWS (ar_lyc cx) (ar_Sc cx) (ar_W cx) (ar_memc cx) (ar_mdc cx) (ar_E cx) ars_pre_ar ars_E_app).
  - exact (fmiss_side SEGS B (ar_lyc cx) (ar_Sc cx) (ar_W cx) (ar_memc cx) (ar_mdc cx) AR_CID fpos ars_pre_ar
      ltac:(unfold AR_CID; lia) Hfp HNIN).
Qed.

(* THE INVARIANT a stage carries: ar_base without the registers and the machine state's shape *)
Definition ars_inv (ly : alayout) (S : astate) (W : world SEGS) (m : word -> option byte) (md : Model) : Prop :=
  AJ ly S W m md /\
  frames S = (AR_CID, fpos) :: frames (ar_Sc cx) /\
  (exists fs, S = set_fs fs (ar_Sc cx)) /\
  Permutation (ablocks B ly S) (ablocks B (ar_lyc cx) (ar_Sc cx)) /\
  (forall c q, frame_addr ly c q = frame_addr (ar_lyc cx) c q) /\
  rdword (aview SEGS (w_H W) m) (ar_sp cx - 8) = Some (raZ (ar_regs cx)) /\
  (forall j, 0 <= j < 11 -> rdword (aview SEGS (w_H W) m) (ar_sp cx - 16 - 8 * j) =
     Some (bv_unsigned (getr (ar_regs cx) (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))) /\
  rdword (aview SEGS (w_H W) m) (F + AR_FLAGPTR) = Some FL /\
  akept SEGS B (ar_lyc cx) (ar_Sc cx) (ar_W cx) (ar_memc cx) W m (ar_sp cx - AK) (ar_sp cx) Eacc /\
  m_fds md = m_fds (ar_mdc cx) /\ m_fs md = m_fs (ar_mdc cx) /\
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) m).

Lemma ars_inv_of_base : forall ly S W ms md, ar_base SK B cx fpos ly S W ms md -> ars_inv ly S W (ms_mem ms) md.
Proof.
  intros ly S W ms md HB. unfold ar_base in HB. cbv zeta in HB.
  destruct HB as (_ & _ & _ & _ & _ & HJ & Hfr & _ & Hfs & Hperm & _ & Hfa & _ & _ & _ & _ & _ & _ & _ & _ & _
    & Hra & Hsv & Hfl & _ & _ & HK & Hfds & Hfs' & Hro).
  unfold ars_inv. repeat (split; [assumption|]). assumption.
Qed.

(* the frame and its shadow are present at every state of the invariant *)
Lemma ars_present : forall ly S W m md, ars_inv ly S W m md ->
  (forall a, F <= a < F + AR_FB -> apresent (w_H W) m a) /\
  (forall a, SH <= a < SH + AR_SHN -> apresent (w_H W) m a).
Proof.
  intros ly S W m md (HJ & Hfr & _ & _ & Hfa & _).
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  assert (Hin : In (AR_CID, fpos) (frames S)) by (rewrite Hfr; left; reflexivity).
  destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & _ & HF & HS).
  rewrite (Hfa AR_CID fpos) in HF, HS. change (fs_frame_bytes AR_CID) with 128 in HF, HS.
  change (128 / 8) with 16 in HS.
  split.
  - intros a Ha. exact (proj1 (HF a Ha)).
  - intros a Ha. unfold AR_SHN in Ha.
    replace a with (shadow_addr (frame_addr (ar_lyc cx) AR_CID fpos) + (a - shadow_addr (frame_addr (ar_lyc cx) AR_CID fpos)))
      by ring.
    apply (proj1 (HS (a - shadow_addr (frame_addr (ar_lyc cx) AR_CID fpos))
      ltac:(unfold shadow_addr, ar_SH, ar_F in *; lia))).
Qed.

Lemma ars_base_of_inv : forall ly S W ms md,
  ms_resv ms = None -> ms_svc_pending ms = None -> ms_rom ms = seg_rom SEGS -> ms_fregs ms = fp_regs ->
  ms_fcsr ms = fp_csr ->
  getr (ms_regs ms) 2 = w64 (ar_sp1 cx) -> getr (ms_regs ms) 9 = w64 (ar_sp1 cx) ->
  getr (ms_regs ms) 8 = w64 (ar_sp cx) ->
  getr (ms_regs ms) 18 = w64 F -> getr (ms_regs ms) 26 = w64 F -> getr (ms_regs ms) 25 = w64 SH ->
  getr (ms_regs ms) 3 = getr (ar_regs cx) 3 -> getr (ms_regs ms) 4 = getr (ar_regs cx) 4 ->
  getr (ms_regs ms) 27 = getr (ar_regs cx) 27 ->
  ars_inv ly S W (ms_mem ms) md -> ar_base SK B cx fpos ly S W ms md.
Proof.
  intros ly S W ms md Hr Hs Hrom Hf Hc R2 R9 R8 R18 R26 R25 R3 R4 R27 HI.
  destruct (ars_present ly S W (ms_mem ms) md HI) as [HFp HSp].
  destruct HI as (HJ & Hfr & Hfs & Hperm & Hfa & Hra & Hsv & Hfl & HK & Hfds & Hfs' & Hro).
  unfold ar_base. cbv zeta. repeat (split; [assumption|]). assumption.
Qed.

(* ---- a step of the walk's own code or of a checked runtime call: the invariant at the new memory ---- *)
Lemma ars_inv_step : forall ly S W m md m' md' (X : Z -> Prop),
  ars_inv ly S W m md ->
  AJ ly S W m' md' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a, X a -> (ar_sp cx - AK <= a < ar_sp1 cx) \/ (F + 32 <= a < F + 64) \/ (SH <= a < SH + 16)) ->
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
  m_fds md' = m_fds md -> m_fs md' = m_fs md ->
  ars_inv ly S W m' md'.
Proof.
  intros ly S W m md m' md' X (HJ & Hfr & Hfs & Hperm & Hfa & Hra & Hsv & Hfl & HK & Hfds & Hfs' & Hro)
    HJ' UN HX Hpres Efds Efs.
  destruct ars_win as (W16 & Wc & Wlo & Whi & W47 & S1lo & S1al).
  destruct ars_F as (F1 & F2 & F3 & F4 & F5 & F6).
  destruct ars_SH as (SH1 & SH2 & SH3 & SH3b & SH4 & SH5).
  pose proof asan_consts as ((C1a & C1b) & _).
  pose proof REAC_LINK_ALIAS_READ_AK_val as HK8.
  assert (Hstk : forall a, ar_sp cx - 96 <= a < ar_sp cx -> ~ X a).
  { intros a Ha HXa. destruct (HX a HXa) as [H|[H|H]]; lia. }
  assert (Hflag : forall a, F + 120 <= a < F + 128 -> ~ X a).
  { intros a Ha HXa. destruct (HX a HXa) as [H|[H|H]]; lia. }
  split; [exact HJ'|]. split; [exact Hfr|]. split; [exact Hfs|]. split; [exact Hperm|]. split; [exact Hfa|].
  split.
  { rewrite <- Hra. apply ars_rdword_eq. intros i Hi. apply UN; [lia | apply Hstk; lia]. }
  split.
  { intros j Hj. rewrite <- (Hsv j Hj). apply ars_rdword_eq. intros i Hi. apply UN; [lia | apply Hstk; lia]. }
  split.
  { rewrite <- Hfl. apply ars_rdword_eq. intros i Hi. unfold AR_FLAGPTR in *. apply UN; [lia | apply Hflag; lia]. }
  split.
  { apply (akept_step SK SEGS B LAWS pa_segs_low (ar_lyc cx) (ar_Sc cx) (ar_W cx) (ar_memc cx) (ar_mdc cx) W m W m'
      (ar_sp cx - AK) (ar_sp cx) Eacc Eacc X ars_pre_ar);
      [lia | lia | exact HK | exact UN | intros a _ Ha; exact (Hpres a Ha) | intros a Ha; exact Ha |].
    intros a HXa. destruct (HX a HXa) as [H|[H|H]].
    - right. lia.
    - left. right. left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes AR_CID) with 128.
      unfold ar_F in H. lia.
    - left. right. right. left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes AR_CID / 8) with 16.
      rewrite SH1 in H. unfold ar_F in H. unfold shadow_addr. lia. }
  split; [rewrite Efds; exact Hfds|]. split; [rewrite Efs; exact Hfs'|].
  apply (ars_arodata_eq _ _ _ _ Hro). intros a Hro_a.
  pose proof (pa_img_range a (ars_ro_img a Hro_a)) as Hir.
  unfold pcap_img_end, YImgTop.IMG_TOP in Hir. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in F5.
  apply UN; [lia|]. intros HXa. destruct (HX a HXa) as [H|[H|H]]; lia.
Qed.

(* ---- nl_talk's step: the invariant at its return, from its apost ---- *)
Lemma ars_nl_step : forall ly S W m md ly2 S2 W2 m2 md2 slo1 shi1 (Enl : Z -> Prop),
  ars_inv ly S W m md ->
  AJ ly2 S2 W2 m2 md2 ->
  frames S2 = frames S -> S2 = set_fs (st_fs S2) S -> Permutation (ablocks B ly2 S2) (ablocks B ly S) ->
  m_fds md2 = m_fds md -> m_fs md2 = m_fs md ->
  akept SEGS B ly S W m W2 m2 slo1 shi1 Enl ->
  ar_sp cx - AK <= slo1 -> shi1 <= ar_sp1 cx ->
  (forall a, Enl a -> ar_E cx a) ->
  ars_inv ly2 S2 W2 m2 md2.
Proof.
  intros ly S W m md ly2 S2 W2 m2 md2 slo1 shi1 Enl (HJ & Hfr & Hfs & Hperm & Hfa & Hra & Hsv & Hfl & HK & Hfds & Hfs'
    & Hro) HJ2 Hfr2 Hset2 Hperm2 Efds Efs HK2 Hslo Hshi HEnl.
  destruct ars_win as (W16 & Wc & Wlo & Whi & W47 & S1lo & S1al).
  destruct ars_F as (F1 & F2 & F3 & F4 & F5 & F6).
  pose proof asan_consts as ((C1a & C1b) & _).
  pose proof REAC_LINK_ALIAS_READ_AK_val as HK8.
  destruct ars_pre_bufs as (KF & AF).
  pose proof HK2 as (L1 & _ & L3 & L4 & _ & _).
  assert (Hfa2 : forall c q, frame_addr ly2 c q = frame_addr (ar_lyc cx) c q).
  { intros c q. rewrite (aj_frame_addr SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 c q).
    rewrite (aj_frame_addr SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ars_pre_j c q). reflexivity. }
  split; [exact HJ2|].
  split; [rewrite Hfr2; exact Hfr|].
  split; [exists (st_fs S2); apply (set_fs_trans S); [apply set_fs_of_exists; exact Hfs | exact Hset2]|].
  split; [exact (Permutation_trans Hperm2 Hperm)|].
  split; [exact Hfa2|].
  (* the save slots: above the callee's window, in none of its write set *)
  assert (Hsw : forall a, ar_sp cx - 96 <= a < ar_sp cx -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W) m a).
  { intros a Ha. apply L1; [lia | lia |]. intros HE. apply HEnl in HE. apply (arx_E_iff cx) in HE.
    destruct HE as [HE | [(Hk0 & HE) | (Ha0 & HE)]].
    - arx_c. lia.
    - destruct (KF Hk0) as (Hf & _). unfold apart_frame in Hf. change (spZ (ar_regs cx)) with (ar_sp cx) in Hf. lia.
    - destruct (AF Ha0) as (Hf & _). unfold apart_frame in Hf. change (spZ (ar_regs cx)) with (ar_sp cx) in Hf. lia. }
  split. { rewrite <- Hra. apply ars_rdword_eq. intros i Hi. apply Hsw. lia. }
  split. { intros j Hj. rewrite <- (Hsv j Hj). apply ars_rdword_eq. intros i Hi. apply Hsw. lia. }
  split.
  { rewrite <- Hfl. apply ars_rdword_eq. intros i Hi. unfold AR_FLAGPTR.
    assert (Hin : In (AR_CID, fpos) (frames S)) by (rewrite Hfr; left; reflexivity).
    assert (HAS : aside_rng (ar_lyc cx) AR_CID fpos (F + 120 + i)).
    { left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes AR_CID) with 128. unfold ar_F. lia. }
    apply (L4 AR_CID fpos (F + 120 + i) Hin).
    - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite (Hfa AR_CID fpos). change (fs_frame_bytes AR_CID) with 128.
      unfold ar_F. lia.
    - intros HE. apply HEnl in HE. pose proof HE as HE'. apply (arx_E_iff cx) in HE'.
      destruct HE' as [HG | [(Hk0 & Hk) | (Ha0 & Ha)]].
      + unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in F5. arx_c. lia.
      + exact (arx_buf_not_side SK B LAWS cx fpos HPRE HNIN HS1 1 2 (F + 120 + i)
          (or_introl (conj eq_refl eq_refl)) Hk0 ltac:(lia) Hk HAS).
      + exact (arx_buf_not_side SK B LAWS cx fpos HPRE HNIN HS1 3 4 (F + 120 + i)
          (or_intror (conj eq_refl eq_refl)) Ha0 ltac:(lia) Ha HAS). }
  split.
  { apply (akept_trans_ly SK SEGS B LAWS pa_segs_low (ar_lyc cx) (ar_Sc cx) (ar_W cx) (ar_memc cx) ly S W m W2 m2
      (ar_sp cx - AK) (ar_sp cx) slo1 shi1 Eacc Enl Eacc);
      [lia | lia | exact HK | exact HK2 | lia | lia
      | intros b0 m0 Hb; exact (Permutation_in _ (Permutation_sym Hperm) Hb)
      | intros f Hf; rewrite Hfr; right; exact Hf
      | exact Hfa
      | intros a Ha; exact Ha
      | intros a Ha; left; exact (HEnl a Ha)]. }
  split; [rewrite Efds; exact Hfds|]. split; [rewrite Efs; exact Hfs'|].
  intros a Ha Ho He.
  rewrite (L3 a (ars_ro_img a Ha) Ho He (fun HE => ars_pre_nro a (HEnl a HE) Ha)).
  exact (Hro a Ha Ho He).
Qed.

(* the shadow facts of a range of the read set or of the write set, from the call to a state of the invariant *)
Lemma ars_shadow_at : forall ly S W m md p n, ars_inv ly S W m md -> 0 < n ->
  (forall x, p <= x < p + n -> sclass SEGS B (ar_lyc cx) (ar_Sc cx) x) ->
  range_addressable (aview SEGS (w_H (ar_W cx)) (ar_memc cx)) SHADOW_OFF p n ->
  shadow_hull_vis (aview SEGS (w_H (ar_W cx)) (ar_memc cx)) p n ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF p n /\ shadow_hull_vis (aview SEGS (w_H W) m) p n.
Proof.
  intros ly S W m md p n (HJ & _ & _ & Hperm & _ & _ & _ & _ & HK & _) Hn Hc HR HH.
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  destruct (aj_stk_row_eq SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [El Eh].
  destruct (aj_stk_row_eq SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ars_pre_j) as [Elc Ehc].
  apply (shadow_transport SEGS B LAWS TB pa_img_range (ar_lyc cx) (ar_Sc cx) (ar_W cx) (ar_memc cx) (ar_mdc cx)
    ly S W m md (ar_sp cx - AK) (ar_sp cx) Eacc p n ars_pre_ar HAR);
    [congruence | congruence | | exact HK | exact ars_fmiss | exact Hn | exact Hc
    | exact HR | exact HH].
  intros b0 m0 Hb. exact (Permutation_in _ (Permutation_sym Hperm) Hb).
Qed.

(* the shadow of image bytes is the same at every AR state (LinkWalkShadow.v img_sh_eq) *)
Lemma ars_img_ra : forall ly S W m md p n, ars_inv ly S W m md ->
  (forall x, p <= x < p + n -> in_img SEGS x) ->
  range_addressable (aview SEGS (w_H (ar_W cx)) (ar_memc cx)) SHADOW_OFF p n ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF p n.
Proof.
  intros ly S W m md p n (HJ & _) Hi HR x Hx.
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (M2 & _).
  pose proof ars_pre_ar as (M1 & _).
  destruct (HR x Hx) as (v & Hv & Hok). exists v. split; [|exact Hok].
  pose proof (pa_img_range x (Hi x Hx)) as Hr. unfold pcap_img_end, YImgTop.IMG_TOP in Hr.
  destruct (img_sh_eq B TB _ _ _ _ _ _ (shadow_of_addr SHADOW_OFF x) M1 M2
    ltac:(unfold shadow_of_addr, SHADOW_OFF; lia)) as [Eq _].
  rewrite Eq. exact Hv.
Qed.

Lemma ars_img_hull : forall ly S W m md p n, ars_inv ly S W m md ->
  0x10000 <= p -> p + n <= 0x654000 -> 0 < n -> shadow_hull_vis (aview SEGS (w_H W) m) p n.
Proof.
  intros ly S W m md p n (HJ & _) Hp Hpn Hn s Hs.
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (M2 & _).
  destruct (img_sh_eq B TB _ _ _ _ _ _ s M2 M2 ltac:(unfold shadow_addr, SHADOW_OFF in *; lia)) as [_ Hv].
  exact Hv.
Qed.

(* the facts nl_talk's Post gives of the kernel's bytes and of the two buffers, as the EXIT cut reads them *)
Definition ars_nlpost (W : world SEGS) (m : word -> option byte) : Prop :=
  (exists kbs', anlk_at SEGS (rdW W m) LA_G_NL kbs' /\ nlk_wf kbs' /\ nk_chunks kbs' = nk_chunks kbs /\
     nk_end_errno kbs' = nk_end_errno kbs /\ nk_n_if kbs' = nk_n_if kbs /\ nk_socket_errno kbs' = 0 /\
     nk_send_errno kbs' = k_send (talk_after K0) /\ nk_next kbs' = Z.of_nat (k_next (talk_after K0)) /\
     nk_sent kbs' = (if talk_owes K0 then owe (nk_sent kbs) (req_read IDX) else nk_sent kbs) /\
     nk_n_sent kbs' = Z.of_nat (length (nk_sent kbs')) /\ nk_open kbs' = 0 /\ nk_misuse kbs' = nk_misuse kbs /\
     nk_opened kbs' - nk_closed kbs' = nk_opened kbs - nk_closed kbs /\
     (nk_socket_errno kbs <> 0 -> nk_opened kbs' = nk_opened kbs) /\
     (nk_socket_errno kbs = 0 -> nk_opened kbs' = nk_opened kbs + 1)) /\
  (ar_kind cx <> 0 -> 1 <= ar_kn cx ->
     acstr_at SEGS (rdW W m) (ar_kind cx) (text_of_attr (a_kind (talk_attrs K0)) (ar_kn cx))) /\
  (ar_alias cx <> 0 -> 1 <= ar_an cx ->
     acstr_at SEGS (rdW W m) (ar_alias cx) (text_of_attr (a_alias (talk_attrs K0)) (ar_an cx))) /\
  (ar_kind cx <> 0 -> 1 <= ar_kn cx -> abuf SEGS (rdW W m) (ar_kind cx) (ar_kn cx)) /\
  (ar_alias cx <> 0 -> 1 <= ar_an cx -> abuf SEGS (rdW W m) (ar_alias cx) (ar_an cx)).

(* the buffers and g_nl across a step that changes only bytes of the frame and of the window *)
Lemma ars_bufs_keep : forall (W : world SEGS) m m',
  ar_bufs_nul cx W m ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ aside_rng (ar_lyc cx) AR_CID fpos a -> ~ (ar_sp cx - AK <= a < ar_sp cx) ->
     aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
  ar_bufs_nul cx W m'.
Proof.
  intros W m m' HBN UN Hp. unfold ar_bufs_nul, ar_kind, ar_kn, ar_alias, ar_an in HBN |- *.
  destruct HBN as (BK & BA). destruct ars_pre_bufs as (KF & AF).
  assert (Hbuf : forall i j, (i = 1 /\ j = 2 \/ i = 3 /\ j = 4) -> aarg (ar_regs cx) i <> 0 -> 1 <= aarg (ar_regs cx) j ->
    forall x, aarg (ar_regs cx) i <= x < aarg (ar_regs cx) i + aarg (ar_regs cx) j ->
    aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x).
  { intros i j Hij H0 H1 x Hx.
    pose proof (ars_aarg_rng (ar_regs cx) i) as Ri. pose proof (ars_aarg_rng (ar_regs cx) j) as Rj.
    assert (Hfr : apart_frame (ar_regs cx) AK (aarg (ar_regs cx) i) (aarg (ar_regs cx) j)).
    { destruct Hij as [(-> & ->) | (-> & ->)]; [exact (proj1 (KF H0)) | exact (proj1 (AF H0))]. }
    unfold apart_frame in Hfr. change (spZ (ar_regs cx)) with (ar_sp cx) in Hfr.
    pose proof ars_win as (_ & _ & _ & _ & W47 & _).
    apply UN.
    - destruct Hij as [(-> & ->) | (-> & ->)];
        [destruct (BK H0 H1) as (_ & (junk & L & (Ha & Hl & _) & _)) | destruct (BA H0 H1) as (_ & (junk & L & (Ha & Hl & _) & _))];
        lia.
    - exact (arx_buf_not_side SK B LAWS cx fpos HPRE HNIN HS1 i j x Hij H0 H1 Hx).
    - lia. }
  split.
  - intros H0 H1. destruct (BK H0 H1) as (C & Bf). split.
    + apply (ars_acstr_vkeep W m m' _ _ C). intros x Hx. cbn [length Z.of_nat] in Hx.
      apply (Hbuf 1 2 (or_introl (conj eq_refl eq_refl)) H0 H1). lia.
    + apply (ars_abuf_vkeep W m m' _ _ Bf); [exact (Hbuf 1 2 (or_introl (conj eq_refl eq_refl)) H0 H1)|].
      intros x _ Hx. exact (Hp x Hx).
  - intros H0 H1. destruct (BA H0 H1) as (C & Bf). split.
    + apply (ars_acstr_vkeep W m m' _ _ C). intros x Hx. cbn [length Z.of_nat] in Hx.
      apply (Hbuf 3 4 (or_intror (conj eq_refl eq_refl)) H0 H1). lia.
    + apply (ars_abuf_vkeep W m m' _ _ Bf); [exact (Hbuf 3 4 (or_intror (conj eq_refl eq_refl)) H0 H1)|].
      intros x _ Hx. exact (Hp x Hx).
Qed.

Lemma ars_gnl_keep : forall (W : world SEGS) m m',
  ar_gnl_kept cx W m ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ aside_rng (ar_lyc cx) AR_CID fpos a -> ~ (ar_sp cx - AK <= a < ar_sp cx) ->
     aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  ar_gnl_kept cx W m'.
Proof.
  intros W m m' HG UN a Ha. rewrite <- (HG a Ha).
  pose proof ars_win as (_ & Wc & Wlo & _ & _ & _ & _). pose proof asan_consts as ((C1a & C1b) & _).
  pose proof REAC_LINK_ALIAS_READ_AK_val as HK8.
  apply UN; [arx_c; lia | exact (arx_gnl_not_side SK B LAWS TB HSEGS cx fpos HS1 a Ha) | arx_c; lia].
Qed.

(* ==========================================================================
   2. STAGE 3, after nl_talk (+0x1e0 .. +0x1f4): the request's shadow := 0xf8, to the EXIT cut
   ========================================================================== *)
Lemma ars_stage3 : forall ly S W (R : bvmap 5 word) m md,
  ars_inv ly S W m md ->
  getr R 2 = w64 (ar_sp1 cx) -> getr R 9 = w64 (ar_sp1 cx) -> getr R 8 = w64 (ar_sp cx) ->
  getr R 18 = w64 F -> getr R 26 = w64 F -> getr R 25 = w64 SH ->
  getr R 3 = getr (ar_regs cx) 3 -> getr R 4 = getr (ar_regs cx) 4 -> getr R 27 = getr (ar_regs cx) 27 ->
  getr R 10 = w64 (talk_rc_lib K0) ->
  ars_nlpost W m ->
  SRr SEGS W (mkCfg (mkst R (Z_to_bv 64 (BASE + (AF_reac_link_alias_read + 0x1e0))) m (seg_rom SEGS)) md)
    (ar_post SK B cx).
Proof.
  intros ly S W R m md HI R2 R9 R8 R18 R26 R25 R3 R4 R27 R10 HNL.
  pose proof HI as (HJ & _ & _ & _ & Hfa & _).
  destruct ars_SH as (SH1 & SH2 & SH3 & SH3b & SH4 & SH5).
  pose proof asan_consts as ((C1a & C1b) & _).
  destruct (ars_present ly S W m md HI) as [_ HSp].
  assert (HEI : img_env VAL A_LIM (Eimg (Ereg R []))) by apply Eimg_env.
  assert (U25 : bv_unsigned (ew (Eimg (Ereg R [])) 25) = SH) by (apply (ars_U R 25 (25%bv : bv 5)); [reflexivity | exact R25 | lia]).
  assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg R [])) ars_ss3
    (restrict (w_H W) (mkst R (Z_to_bv 64 (BASE + (AF_reac_link_alias_read + 0x1e0))) m (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ars_ss3. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, ars_sh_r.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U25.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (YCbq.apresent_writable SEGS). apply HSp. unfold AR_SHN. lia.
    - cbn [pairwise_disjoint all_disjoint]. split; exact I.
    - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I]. }
  ars_run_to (paj_run_to_plain_x SK B LAWS (ar_G cx) ars_pre_g (ar_XO cx) (ar_OUT cx)) HS HJ
    (AF_reac_link_alias_read + 0x1fc).
  { apply awr_ok_x_cons; [|apply awr_ok_x_nil]. intros a Ha. unfold ars_sh_r in Ha.
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U25 in Ha. left.
    apply (aj_gx_awr_frame SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AR_CID fpos a HJ
      (or_introl eq_refl)).
    right. unfold in_zr. cbn [fst snd]. rewrite (Hfa AR_CID fpos). change (fs_frame_bytes AR_CID / 8) with 16.
    rewrite SH1 in Ha. unfold ar_F in Ha. unfold shadow_addr. lia. }
  intros ms' mat' HS' HJ' HF HF' HG'. cbn [ms_mem mkst] in HF, HF', HG'.
  pose proof (st_ok_pi_restrict_mkst (w_H W) _ _ ms' HS' eq_refl) as Ems. cbn [ss_pc] in Ems.
  prreg_raw HS' (2%bv : bv 5) Q2. prreg_raw HS' (9%bv : bv 5) Q9. prreg_raw HS' (8%bv : bv 5) Q8.
  prreg_raw HS' (18%bv : bv 5) Q18. prreg_raw HS' (26%bv : bv 5) Q26. prreg_raw HS' (25%bv : bv 5) Q25.
  prreg_raw HS' (3%bv : bv 5) Q3. prreg_raw HS' (4%bv : bv 5) Q4. prreg_raw HS' (27%bv : bv 5) Q27.
  prreg_raw HS' (10%bv : bv 5) Q10.
  rewrite (ars_atom R 2 (2%bv : bv 5) eq_refl) in Q2. rewrite (ars_atom R 9 (9%bv : bv 5) eq_refl) in Q9.
  rewrite (ars_atom R 8 (8%bv : bv 5) eq_refl) in Q8. rewrite (ars_atom R 18 (18%bv : bv 5) eq_refl) in Q18.
  rewrite (ars_atom R 26 (26%bv : bv 5) eq_refl) in Q26. rewrite (ars_atom R 25 (25%bv : bv 5) eq_refl) in Q25.
  rewrite (ars_atom R 3 (3%bv : bv 5) eq_refl) in Q3. rewrite (ars_atom R 4 (4%bv : bv 5) eq_refl) in Q4.
  rewrite (ars_atom R 27 (27%bv : bv 5) eq_refl) in Q27. rewrite (ars_atom R 10 (10%bv : bv 5) eq_refl) in Q10.
  set (mdx := with_vm_backing (m_vm_lazy md) mat' md) in *.
  destruct (wvb_fds_fs (m_vm_lazy md) mat' md) as [Efds Efs]. fold mdx in Efds, Efs.
  (* the run wrote SH + 4 .. SH + 7 only *)
  assert (HNW : forall x, 0 <= x < 2 ^ 64 -> ~ (SH + 4 <= x < SH + 8) -> aview SEGS (w_H W) (ms_mem ms') x = aview SEGS (w_H W) m x).
  { intros x Hx Hn. apply (ars_frame_aview _ _ (w_H W) m (ms_mem ms') x HF' Hx). intros (r & [<- | []] & Hr).
    unfold ars_sh_r in Hr. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite U25 in Hr. lia. }
  assert (HSD : forall x, SH + 4 <= x < SH + 8 -> aside_rng (ar_lyc cx) AR_CID fpos x).
  { intros x Hx. right; left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes AR_CID / 8) with 16.
    rewrite SH1 in Hx. unfold ar_F in Hx. unfold shadow_addr. lia. }
  assert (HIx : ars_inv ly S W (ms_mem ms') mdx).
  { apply (ars_inv_step ly S W m md (ms_mem ms') mdx (fun a => SH + 4 <= a < SH + 8) HI HJ').
    - exact HNW.
    - intros a Ha. right; right. lia.
    - intros a Ha. exact (apresent_grows _ _ _ a HG' Ha).
    - exact Efds.
    - exact Efs. }
  assert (HNS : forall x, 0 <= x < 2 ^ 64 -> ~ aside_rng (ar_lyc cx) AR_CID fpos x ->
    aview SEGS (w_H W) (ms_mem ms') x = aview SEGS (w_H W) m x).
  { intros x Hx Hn. apply HNW; [exact Hx|]. intros Hs. exact (Hn (HSD x Hs)). }
  destruct (ms_shape_mkst SEGS ms' _ _ _ Ems) as (Sh1 & Sh2 & Sh3 & Sh4 & Sh5 & Sh6).
  apply (EXIT cx fpos ly S W ms' mdx HPRE).
  exists (talk_rc_lib K0).
  split; [rewrite Sh6; unfold w64, AR_CUT_EXIT; reflexivity|].
  split; [rewrite Q10; exact R10|].
  split.
  { apply ars_base_of_inv; try assumption.
    - rewrite Q2; exact R2.
    - rewrite Q9; exact R9.
    - rewrite Q8; exact R8.
    - rewrite Q18; exact R18.
    - rewrite Q26; exact R26.
    - rewrite Q25; exact R25.
    - rewrite Q3; exact R3.
    - rewrite Q4; exact R4.
    - rewrite Q27; exact R27. }
  (* the Post's facts at the EXIT cut *)
  pose proof HIx as (_ & _ & _ & _ & _ & _ & _ & _ & HKx & _).
  intros kbs2 tab2 nm2 NK2 IT2 SN2. cbv zeta.
  assert (kbs2 = kbs) by exact (ar_anlk_unique SEGS _ _ _ _ NK2 HNK). subst kbs2.
  assert (tab2 = tab) by exact (ar_aiftab_unique SEGS _ _ _ _ IT2 HIT). subst tab2.
  assert (nm2 = Some sn) by (apply (ar_astr_arg_unique SEGS _ _ _ _ SN2); split; [exact HN0 | exact HSN]).
  subst nm2.
  rewrite (ar_read_lib_talk tab sn (ar_kn cx) (ar_an cx) (nk_sent kbs) K0 HSNE HIDX).
  cbn [r_rc r_kind r_alias r_reqs r_state].
  destruct HNL as ((kbs' & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15)
    & KS & AS & KB & AB).
  split; [reflexivity|].
  split.
  { exists kbs'. split.
    { apply (ars_anlk_vkeep W m (ms_mem ms') kbs' N1). intros x Hx. apply HNS; [arx_c; lia|].
      exact (arx_gnl_not_side SK B LAWS TB HSEGS cx fpos HS1 x Hx). }
    split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [exact N5|].
    split; [exact (arx_tab_kept SK B LAWS TB HSEGS cx fpos HPRE HNIN HS1 kbs tab W (ms_mem ms') kbs' HNK HIT HKx N5)|].
    split; [exact N8|]. split; [rewrite ar_talk_after_sock; exact N6|]. split; [exact N7|]. split; [exact N9|].
    split; [rewrite N10, N9; reflexivity|]. split; [exact N11|]. split; [exact N12|]. split; [exact N13|].
    split; [destruct (Z.eq_dec (nk_socket_errno kbs) 0) as [E0|E0]; [rewrite (N15 E0) | rewrite (N14 E0)]; lia|].
    intros [H|[H|H]]; [discriminate H | injection H as H; exfalso; exact (HSNE H) | exfalso; exact (HIDX (H sn eq_refl))]. }
  unfold ar_kind, ar_kn, ar_alias, ar_an in KS, AS, KB, AB |- *.
  assert (Hbx : forall i j x, (i = 1 /\ j = 2 \/ i = 3 /\ j = 4) -> aarg (ar_regs cx) i <> 0 -> 1 <= aarg (ar_regs cx) j ->
    aarg (ar_regs cx) i <= x < aarg (ar_regs cx) i + aarg (ar_regs cx) j ->
    aview SEGS (w_H W) (ms_mem ms') x = aview SEGS (w_H W) m x).
  { intros i j x Hij H0 H1 Hx. apply HNS.
    - assert (Hb : abuf SEGS (rdW W m) (aarg (ar_regs cx) i) (aarg (ar_regs cx) j))
        by (destruct Hij as [(-> & ->) | (-> & ->)]; [exact (KB H0 H1) | exact (AB H0 H1)]).
      destruct Hb as (junk & L & (Ha & Hl & _) & _). lia.
    - exact (arx_buf_not_side SK B LAWS cx fpos HPRE HNIN HS1 i j x Hij H0 H1 Hx). }
  split.
  { intros H0 H1. rewrite (proj2 (Z.ltb_ge _ _) H1). pose proof (KS H0 H1) as C.
    pose proof (ars_toa_len (a_kind (talk_attrs K0)) _ H1) as Lc.
    apply (ars_acstr_vkeep W m (ms_mem ms') _ _ C). intros x Hx.
    apply (Hbx 1 2 x (or_introl (conj eq_refl eq_refl)) H0 H1). lia. }
  split.
  { intros H0 H1. rewrite (proj2 (Z.ltb_ge _ _) H1). pose proof (AS H0 H1) as C.
    pose proof (ars_toa_len (a_alias (talk_attrs K0)) _ H1) as Lc.
    apply (ars_acstr_vkeep W m (ms_mem ms') _ _ C). intros x Hx.
    apply (Hbx 3 4 x (or_intror (conj eq_refl eq_refl)) H0 H1). lia. }
  split.
  { intros H0 H1. apply (ars_abuf_vkeep W m (ms_mem ms') _ _ (KB H0 H1)).
    - intros x Hx. exact (Hbx 1 2 x (or_introl (conj eq_refl eq_refl)) H0 H1 Hx).
    - intros x _ Hx. exact (apresent_grows _ _ _ x HG' Hx). }
  { intros H0 H1. apply (ars_abuf_vkeep W m (ms_mem ms') _ _ (AB H0 H1)).
    - intros x Hx. exact (Hbx 3 4 x (or_intror (conj eq_refl eq_refl)) H0 H1 Hx).
    - intros x _ Hx. exact (apresent_grows _ _ _ x HG' Hx). }
Qed.

(* a byte of one of the two buffers is of a class AR pins (a byte of the caller's write set, in application memory) *)
Lemma ars_buf_sclass : forall i j x, (i = 1 /\ j = 2 \/ i = 3 /\ j = 4) ->
  aarg (ar_regs cx) i <> 0 -> 1 <= aarg (ar_regs cx) j ->
  aarg (ar_regs cx) i <= x < aarg (ar_regs cx) i + aarg (ar_regs cx) j ->
  sclass SEGS B (ar_lyc cx) (ar_Sc cx) x.
Proof.
  intros i j x Hij H0 H1 Hx.
  destruct HPRE as (_ & _ & (kbs0 & tab0 & nm0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & KCH & ACH)).
  assert (HE : ar_E cx x /\ amem_range (aarg (ar_regs cx) i) (aarg (ar_regs cx) j)).
  { destruct Hij as [(-> & ->) | (-> & ->)].
    - split; [apply (arx_E_iff cx); right; left; split; assumption | exact (proj1 (KCH H0 H1))].
    - split; [apply (arx_E_iff cx); right; right; split; assumption | exact (proj1 (ACH H0 H1))]. }
  destruct HE as (HE & Hr).
  apply (sclass_of_ajw SK SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x ars_pre_g ars_pre_j (ars_pre_ajw x HE)).
  unfold amem_range in Hr. arx_c. lia.
Qed.

(* ==========================================================================
   3. STAGE 2 (+0x1a4 .. +0x1dc), the request's header words, then nl_talk, then stage 3
   ========================================================================== *)
Lemma ars_stage2 : forall ly S W (R : bvmap 5 word) m md,
  ars_inv ly S W m md ->
  getr R 2 = w64 (ar_sp1 cx) -> getr R 9 = w64 (ar_sp1 cx) -> getr R 8 = w64 (ar_sp cx) ->
  getr R 18 = w64 F -> getr R 26 = w64 F -> getr R 25 = w64 SH ->
  getr R 3 = getr (ar_regs cx) 3 -> getr R 4 = getr (ar_regs cx) 4 -> getr R 27 = getr (ar_regs cx) 27 ->
  getr R 24 = w64 (F + 32) -> getr R 23 = w64 IDX ->
  getr R 19 = w64 (ar_alias cx) -> getr R 20 = w64 (ar_an cx) ->
  getr R 21 = w64 (ar_kind cx) -> getr R 22 = w64 (ar_kn cx) ->
  ar_gnl_kept cx W m -> ar_bufs_nul cx W m ->
  (forall i, 4 <= i < 8 -> aview SEGS (w_H W) m (SH + i) = Some 0) ->
  (forall i, 0 <= i < 20 -> aview SEGS (w_H W) m (F + 44 + i) = Some 0) ->
  SRr SEGS W (mkCfg (mkst R (Z_to_bv 64 (BASE + (AF_reac_link_alias_read + 0x1a4))) m (seg_rom SEGS)) md)
    (ar_post SK B cx).
Proof.
  intros ly S W R m md HI R2 R9 R8 R18 R26 R25 R3 R4 R27 R24 R23 R19 R20 R21 R22 HGK HBN HSZ HRZ.
  pose proof HI as (HJ & Hfr & Hfs & Hperm & Hfa & _).
  destruct ars_win as (W16 & Wc & Wlo & Whi & W47 & S1lo & S1al).
  destruct ars_F as (F1 & F2 & F3 & F4 & F5 & F6).
  destruct ars_SH as (SH1 & SH2 & SH3 & SH3b & SH4 & SH5).
  pose proof asan_consts as ((C1a & C1b) & _).
  pose proof REAC_LINK_ALIAS_READ_AK_val as HK8.
  pose proof (div8_of_mul64 F F3) as (D1 & D2).
  destruct (ars_present ly S W m md HI) as [HFp HSp].
  assert (HEI : img_env VAL A_LIM (Eimg (Ereg R []))) by apply Eimg_env.
  assert (U24 : bv_unsigned (ew (Eimg (Ereg R [])) 24) = F + 32)
    by (apply (ars_U R 24 (24%bv : bv 5)); [reflexivity | exact R24 | lia]).
  assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg R [])) ars_ss2
    (restrict (w_H W) (mkst R (Z_to_bv 64 (BASE + (AF_reac_link_alias_read + 0x1a4))) m (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ars_ss2. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok, ars_reqa_r, ars_reqb_r;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite U24;
        (split; [lia|]); (split; [lia|]); (split; [|apply Forall_nil]);
        intros o Ho; apply (YCbq.apresent_writable SEGS); apply HFp; unfold AR_FB; lia.
    - unfold ars_reqa_r, ars_reqb_r. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U24. repeat split; lia.
    - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I]. }
  ars_run_call (paj_run_call_plain_x SK B LAWS (ar_G cx) ars_pre_g (ar_XO cx) (ar_OUT cx)) HS HJ.
  { apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ars_reqa_r ars_reqb_r]; intros a Ha; rewrite U24 in Ha; left;
      apply (aj_gx_awr_frame SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AR_CID fpos a HJ
        (or_introl eq_refl));
      left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite (Hfa AR_CID fpos); change (fs_frame_bytes AR_CID) with 128;
      unfold ar_F in *; lia. }
  intros ms1 mat1 HS1' HJ1 HF HF' HG'. cbn [ms_mem mkst] in HF, HF', HG'.
  pose proof (st_ok_restrict_mkst SEGS (w_H W) _ _ ms1 HS1' eq_refl) as Ems1. cbn [ss_pc setpc] in Ems1.
  set (mdN := with_vm_backing (m_vm_lazy md) mat1 md) in *.
  sreg HS1' (1%bv : bv 5) Q1. sreg HS1' (2%bv : bv 5) Q2. sreg HS1' (3%bv : bv 5) Q3. sreg HS1' (4%bv : bv 5) Q4.
  sreg HS1' (8%bv : bv 5) Q8. sreg HS1' (9%bv : bv 5) Q9. sreg HS1' (10%bv : bv 5) Q10.
  sreg HS1' (11%bv : bv 5) Q11. sreg HS1' (12%bv : bv 5) Q12. sreg HS1' (13%bv : bv 5) Q13.
  sreg HS1' (14%bv : bv 5) Q14. sreg HS1' (15%bv : bv 5) Q15.
  sreg HS1' (18%bv : bv 5) Q18. sreg HS1' (25%bv : bv 5) Q25. sreg HS1' (26%bv : bv 5) Q26.
  sreg HS1' (27%bv : bv 5) Q27.
  assert (G1 : getr (ms_regs ms1) 1 = Z_to_bv 64 (BASE + (AF_reac_link_alias_read + 0x1e0)))
    by (rewrite Q1; exact (codeptr_val _ (AF_reac_link_alias_read + 0x1e0) HEI)).
  assert (G2 : getr (ms_regs ms1) 2 = w64 (ar_sp1 cx)) by (rewrite Q2, (ars_atom R 2 (2%bv : bv 5) eq_refl); exact R2).
  assert (G3 : getr (ms_regs ms1) 3 = getr (ar_regs cx) 3) by (rewrite Q3, (ars_atom R 3 (3%bv : bv 5) eq_refl); exact R3).
  assert (G4 : getr (ms_regs ms1) 4 = getr (ar_regs cx) 4) by (rewrite Q4, (ars_atom R 4 (4%bv : bv 5) eq_refl); exact R4).
  assert (G8 : getr (ms_regs ms1) 8 = w64 (ar_sp cx)) by (rewrite Q8, (ars_atom R 8 (8%bv : bv 5) eq_refl); exact R8).
  assert (G9 : getr (ms_regs ms1) 9 = w64 (ar_sp1 cx)) by (rewrite Q9, (ars_atom R 9 (9%bv : bv 5) eq_refl); exact R9).
  assert (G10 : getr (ms_regs ms1) 10 = w64 (F + 32))
    by (rewrite Q10, (ars_atom R 24 (24%bv : bv 5) eq_refl); exact R24).
  assert (G11 : getr (ms_regs ms1) 11 = w64 32) by (rewrite Q11; reflexivity).
  assert (G12 : getr (ms_regs ms1) 12 = w64 (ar_kind cx))
    by (rewrite Q12, (ars_atom R 21 (21%bv : bv 5) eq_refl); exact R21).
  assert (G13 : getr (ms_regs ms1) 13 = w64 (ar_kn cx))
    by (rewrite Q13, (ars_atom R 22 (22%bv : bv 5) eq_refl); exact R22).
  assert (G14 : getr (ms_regs ms1) 14 = w64 (ar_alias cx))
    by (rewrite Q14, (ars_atom R 19 (19%bv : bv 5) eq_refl); exact R19).
  assert (G15 : getr (ms_regs ms1) 15 = w64 (ar_an cx))
    by (rewrite Q15, (ars_atom R 20 (20%bv : bv 5) eq_refl); exact R20).
  assert (G18 : getr (ms_regs ms1) 18 = w64 F) by (rewrite Q18, (ars_atom R 18 (18%bv : bv 5) eq_refl); exact R18).
  assert (G25 : getr (ms_regs ms1) 25 = w64 SH) by (rewrite Q25, (ars_atom R 25 (25%bv : bv 5) eq_refl); exact R25).
  assert (G26 : getr (ms_regs ms1) 26 = w64 F) by (rewrite Q26, (ars_atom R 26 (26%bv : bv 5) eq_refl); exact R26).
  assert (G27 : getr (ms_regs ms1) 27 = getr (ar_regs cx) 27)
    by (rewrite Q27, (ars_atom R 27 (27%bv : bv 5) eq_refl); exact R27).
  clear Q1 Q2 Q3 Q4 Q8 Q9 Q10 Q11 Q12 Q13 Q14 Q15 Q18 Q25 Q26 Q27.
  assert (HspN : spZ (ms_regs ms1) = ar_sp1 cx) by (unfold spZ; rewrite G2; apply unsigned_lit_small; lia).
  (* the bytes the run wrote: the request's header words *)
  assert (UN2 : forall x, 0 <= x < 2 ^ 64 -> ~ (F + 32 <= x < F + 44 \/ F + 52 <= x < F + 56) ->
    aview SEGS (w_H W) (ms_mem ms1) x = aview SEGS (w_H W) m x).
  { intros x Hx Hn. apply (ars_frame_aview _ _ (w_H W) m (ms_mem ms1) x HF' Hx).
    intros (r & Hin & Hr). unfold ars_ss2 in Hin. cbn [ss_mem In] in Hin.
    destruct Hin as [<- | [<- | []]]; unfold ars_reqa_r, ars_reqb_r in Hr;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite U24 in Hr; lia. }
  assert (UNs : forall x, 0 <= x < 2 ^ 64 -> ~ aside_rng (ar_lyc cx) AR_CID fpos x ->
    ~ (ar_sp cx - AK <= x < ar_sp cx) -> aview SEGS (w_H W) (ms_mem ms1) x = aview SEGS (w_H W) m x).
  { intros x Hx Hn _. apply UN2; [exact Hx|]. intros Hw. apply Hn. left. unfold in_zr, frame_rng. cbn [fst snd].
    change (fs_frame_bytes AR_CID) with 128. unfold ar_F in *. lia. }
  assert (HIN : ars_inv ly S W (ms_mem ms1) mdN).
  { apply (ars_inv_step ly S W m md (ms_mem ms1) mdN (fun a => F + 32 <= a < F + 44 \/ F + 52 <= a < F + 56) HI HJ1).
    - exact UN2.
    - intros a Ha. right; left. lia.
    - intros a Ha. exact (apresent_grows _ _ _ a HG' Ha).
    - subst mdN. exact (proj1 (wvb_fds_fs _ _ _)).
    - subst mdN. exact (proj2 (wvb_fds_fs _ _ _)). }
  pose proof (ars_gnl_keep W m (ms_mem ms1) HGK UNs) as HGKn.
  pose proof (ars_bufs_keep W m (ms_mem ms1) HBN UNs (fun a Ha => apresent_grows _ _ _ a HG' Ha)) as HBNn.
  assert (HSZn : forall i, 4 <= i < 8 -> aview SEGS (w_H W) (ms_mem ms1) (SH + i) = Some 0).
  { intros i Hi. rewrite UN2; [exact (HSZ i Hi) | lia | lia]. }
  destruct (ars_present ly S W (ms_mem ms1) mdN HIN) as [HFpN HSpN].
  pose proof HIN as (_ & _ & _ & _ & _ & _ & _ & _ & HKN & _ & _ & HRON).
  (* the request, as nl_talk's Pre reads it: req_read IDX *)
  assert (HIX : 0 <= IDX < 2 ^ 31).
  { apply ar_index_of_range. intros i n ix Hi. destruct HIT as (_ & _ & EIT). exact (proj1 (EIT i n ix Hi)). }
  pose proof (st_ok_region_nth _ _ _ 0 _ HS1' eq_refl) as HRA. cbn [ms_mem restrict] in HRA.
  pose proof (st_ok_region_nth _ _ _ 1 _ HS1' eq_refl) as HRB. cbn [ms_mem restrict] in HRB.
  pose proof (field_of_region _ _ _ _ _ _ _ _ _ 0 4%N (SLit 32) 32 HRA U24 ltac:(ars_in) eq_refl
    ltac:(cbn; lia) ltac:(cbn; lia)) as V0.
  pose proof (field_of_region _ _ _ _ _ _ _ _ _ 4 4%N (SLit 65554) 65554 HRA U24 ltac:(ars_in) eq_refl
    ltac:(cbn; lia) ltac:(cbn; lia)) as V1.
  pose proof (field_of_region _ _ _ _ _ _ _ _ _ 8 4%N (SLit 1) 1 HRA U24 ltac:(ars_in) eq_refl
    ltac:(cbn; lia) ltac:(cbn; lia)) as V2.
  pose proof (field_of_region _ _ _ _ _ _ _ _ _ 20 4%N (SOff 23 0) IDX HRB U24 ltac:(ars_in)
    ltac:(rewrite (ars_atom R 23 (23%bv : bv 5) eq_refl); exact R23) ltac:(cbn; lia) ltac:(cbn; lia)) as V3.
  rewrite Z.add_0_r in V0.
  assert (HREQ : abytes SEGS (rdW W (ms_mem ms1)) (F + 32) (req_read IDX)).
  { apply (ar_req_bytes SEGS _ (F + 32) IDX HIX ltac:(lia) ltac:(lia) V0 V1 V2 V3).
    - intros i Hi. apply ars_aview0. rewrite UN2; [|lia|lia]. replace (F + 32 + 12 + i) with (F + 44 + i) by lia.
      apply HRZ. lia.
    - intros i Hi. apply ars_aview0. rewrite UN2; [|lia|lia]. replace (F + 32 + 24 + i) with (F + 44 + (12 + i)) by lia.
      apply HRZ. lia. }
  (* nl_talk's arguments *)
  assert (AN0 : aarg (ms_regs ms1) 0 = F + 32)
    by (apply (ars_aarg _ 0 (10%bv : bv 5)); [apply bv_eq; reflexivity | exact G10 | lia]).
  assert (AN1 : aarg (ms_regs ms1) 1 = 32)
    by (apply (ars_aarg _ 1 (11%bv : bv 5)); [apply bv_eq; reflexivity | exact G11 | lia]).
  assert (AN2 : aarg (ms_regs ms1) 2 = aarg (ar_regs cx) 1)
    by (apply (ars_aarg _ 2 (12%bv : bv 5)); [apply bv_eq; reflexivity | exact G12 | apply ars_aarg_rng]).
  assert (AN3 : aarg (ms_regs ms1) 3 = aarg (ar_regs cx) 2)
    by (apply (ars_aarg _ 3 (13%bv : bv 5)); [apply bv_eq; reflexivity | exact G13 | apply ars_aarg_rng]).
  assert (AN4 : aarg (ms_regs ms1) 4 = aarg (ar_regs cx) 3)
    by (apply (ars_aarg _ 4 (14%bv : bv 5)); [apply bv_eq; reflexivity | exact G14 | apply ars_aarg_rng]).
  assert (AN5 : aarg (ms_regs ms1) 5 = aarg (ar_regs cx) 4)
    by (apply (ars_aarg _ 5 (15%bv : bv 5)); [apply bv_eq; reflexivity | exact G15 | apply ars_aarg_rng]).
  assert (EWR : nl_talk_awr (ms_regs ms1) (rdW W (ms_mem ms1)) = ar_wr cx)
    by (unfold nl_talk_awr, ar_wr, reac_link_alias_read_awr; rewrite AN2, AN3, AN4, AN5; reflexivity).
  assert (HNA : NL_TALK_AK = 8448) by reflexivity.
  pose proof HPRE as ((_ & _ & _ & _ & _ & Hgp & Htp & _ & _ & _ & Hev & Hside & _ & _) & _ &
    (kbs0 & tab0 & nm0 & NK0 & WF0 & OP0 & O10 & C10 & IT0 & RA0 & HV0 & ERR0 & SN0 & BK0 & BA0 & TABC & NMAP & BB & EK
     & EA & NMC & KF & AF & KCH & ACH)).
  assert (kbs0 = kbs) by exact (ar_anlk_unique SEGS _ _ _ _ NK0 HNK). subst kbs0.
  pose proof pa_B_ok as HBo. pose proof (pa_base_lo (PL := PL_link) (PI := PI)) as HBl.
  assert (HAPN : apre SK SEGS PCAP_RLO PCAP_RHI B NL_TALK_AK 0 NL_TALK_ASIDE
    (nl_talk_awr (ms_regs ms1) (rdW W (ms_mem ms1)))
    (ar_G cx) (ar_XO cx) (ar_OUT cx) (ar_STK cx) (ar_sp0 cx) (ar_FP cx) (ar_ly cx) (ar_S cx) (ar_W0 cx) (ar_mem0 cx)
    (ar_md0 cx) ((AR_CID, fpos) :: ar_own cx) ly S W (ms_mem ms1) mdN (ar_k cx) (ms_regs ms1)).
  { rewrite EWR. unfold apre.
    split; [exact HJ1|]. split; [exact ars_pre_g|]. split; [exact HRON|].
    split; [rewrite G1; apply ret_ok_codeptr_v; [unfold AF_reac_link_alias_read; lia | reflexivity]|].
    split; [unfold raZ; rewrite G1, unsigned_lit_small by (unfold AF_reac_link_alias_read; lia);
            unfold AF_reac_link_alias_read; lia|].
    split; [rewrite G3; exact Hgp|]. split; [rewrite G4; exact Htp|].
    split; [rewrite HspN; exact S1al|]. split; [rewrite HspN, HNA; lia|]. split; [rewrite HspN; lia|].
    split; [exact Hev|].
    split.
    { apply (aside_room_push (ar_Sc cx) S [(1, 1); (9, 1)] NL_TALK_ASIDE AR_CID fpos Hfr Hside).
      intros c' d' Hin. unfold NL_TALK_ASIDE in Hin. destruct Hin as [Hcd | []]. injection Hcd as <- <-.
      exists 1. split; [right; left; reflexivity | cbn; lia]. }
    split.
    { intros a Ha.
      apply (ajw_mono B (ar_G cx) (ar_XO cx) (ar_OUT cx) (ar_STK cx) (ar_sp0 cx) (ar_FP cx) (ar_ly cx) (ar_S cx)
        (ar_lyc cx) (ar_Sc cx) (ar_own cx) ly S ((AR_CID, fpos) :: ar_own cx) a (ars_pre_ajw a Ha)).
      - intros b0 m0 Hb. exact (Permutation_in _ (Permutation_sym Hperm) Hb).
      - intros x Hx. right. exact Hx.
      - exact Hfa. }
    intros a Ha. exact (ars_pre_nro a Ha). }
  assert (HRDN : forall a, nl_talk_ard (ms_regs ms1) (rdW W (ms_mem ms1)) a ->
    akb SEGS B ly S (spZ (ms_regs ms1) - NL_TALK_AK) (spZ (ms_regs ms1)) a).
  { intros a Ha. unfold nl_talk_ard, rd_ivl in Ha. rewrite AN0, AN1 in Ha.
    right; right; right. exists AR_CID, fpos. split; [rewrite Hfr; left; reflexivity|].
    unfold in_zr, frame_rng. cbn [fst snd]. rewrite (Hfa AR_CID fpos). change (fs_frame_bytes AR_CID) with 128.
    unfold ar_F in *. lia. }
  assert (HNKN : anlk_at SEGS (rdW W (ms_mem ms1)) LA_G_NL kbs).
  { apply (ar_anlk_move SEGS (ar_m0 cx) _ kbs HNK); intros x Hx.
    - unfold ar_m0. apply (YCbq.mbyte_of_aview SEGS). exact (HGKn x Hx).
    - pose proof (LA_G_NL_writable (rdW W (ms_mem ms1)) x ltac:(unfold NK_SIZE in Hx; lia)) as Hw.
      rewrite <- HSEGS in Hw. exact Hw. }
  unfold ar_bufs_nul, ar_kind, ar_kn, ar_alias, ar_an in HBNn. destruct HBNn as (BKn & BAn).
  assert (HPRN : nl_talk_apre SEGS B (ms_regs ms1) (rdW W (ms_mem ms1))).
  { unfold nl_talk_apre. rewrite AN0, AN1, AN2, AN3, AN4, AN5. exists kbs, (req_read IDX).
    split; [exact HNKN|]. split; [exact WF0|]. split; [exact OP0|]. split; [exact O10|]. split; [exact C10|].
    destruct (ars_shadow_at ly S W (ms_mem ms1) mdN LA_G_NL NK_SIZE HIN ltac:(arx_c; lia)
      (fun x Hx => or_intror (or_intror (or_introl (proj1 (arx_gnl_img B TB HSEGS x Hx))))) RA0 HV0) as [RAg HVg].
    split; [exact RAg|]. split; [exact HVg|].
    split.
    { destruct ERR0 as (Etp & Ewr & Era & Efr & Egn).
      split; [exact Etp|]. split; [intros i Hi; apply ars_errno_writable; lia|].
      split; [exact (ars_img_ra ly S W (ms_mem ms1) mdN _ _ HIN (fun x Hx => ars_errno_img x Hx) Era)|].
      split; [|exact Egn]. unfold apart_frame in *. rewrite HspN. change (spZ (ar_regs cx)) with (ar_sp cx) in Efr.
      rewrite HNA. lia. }
    split; [exact HREQ|]. split; [exact (ar_req_read_length IDX)|]. split; [unfold NL_SENT_LEN; lia|].
    split.
    { unfold amem_range. unfold in_app in F4. destruct F4 as (_ & [Hl | (Hh & _)]); [left | right];
        unfold kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia. }
    split.
    { intros x Hx. unfold shadow_of_addr. exists 0. split; [|left; reflexivity].
      replace (SHADOW_OFF + x / 8) with (SH + (x - F) / 8) by (rewrite SH1; lia).
      apply HSZn. lia. }
    split.
    { intros _ s Hs. apply ars_present_vis. apply HSpN. unfold AR_SHN. unfold shadow_addr in Hs. rewrite SH1. lia. }
    split; [unfold apart_frame; rewrite HspN, HNA; left; lia|].
    split; [unfold apart_gnl, off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; arx_c; lia|].
    split; [intros Hk0 Hkn; exact (proj2 (BKn Hk0 Hkn))|].
    split; [intros Ha0 Han; exact (proj2 (BAn Ha0 Han))|].
    split; [exact EK|]. split; [exact EA|]. split; [exact BB|].
    split.
    { intros Hk0. destruct (KF Hk0) as (Hf & Hg). split; [|exact Hg]. unfold apart_frame in *. rewrite HspN, HNA.
      change (spZ (ar_regs cx)) with (ar_sp cx) in Hf. lia. }
    split.
    { intros Ha0. destruct (AF Ha0) as (Hf & Hg). split; [|exact Hg]. unfold apart_frame in *. rewrite HspN, HNA.
      change (spZ (ar_regs cx)) with (ar_sp cx) in Hf. lia. }
    split.
    { intros Hk0 Hkn. destruct (KCH Hk0 Hkn) as (Hr & HRa & HHu). split; [exact Hr|].
      apply (ars_shadow_at ly S W (ms_mem ms1) mdN (aarg (ar_regs cx) 1) (aarg (ar_regs cx) 2) HIN ltac:(lia));
        [|exact HRa | exact HHu].
      intros x Hx. exact (ars_buf_sclass 1 2 x (or_introl (conj eq_refl eq_refl)) Hk0 Hkn Hx). }
    { intros Ha0 Han. destruct (ACH Ha0 Han) as (Hr & HRa & HHu). split; [exact Hr|].
      apply (ars_shadow_at ly S W (ms_mem ms1) mdN (aarg (ar_regs cx) 3) (aarg (ar_regs cx) 4) HIN ltac:(lia));
        [|exact HRa | exact HHu].
      intros x Hx. exact (ars_buf_sclass 3 4 x (or_intror (conj eq_refl eq_refl)) Ha0 Han Hx). } }
  (* ---- +0x1dc: nl_talk ---- *)
  rewrite Ems1.
  replace (pa_sigma LS_nl_talk) with NL_TALK_A by (rewrite (lv_sigma HV); vm_compute; reflexivity).
  eapply SRr_bind.
  { exact (NLT (ar_G cx) (ar_XO cx) (ar_OUT cx) (ar_STK cx) (ar_sp0 cx) (ar_FP cx) (ar_ly cx) (ar_S cx) (ar_W0 cx)
      (ar_mem0 cx) (ar_md0 cx) ((AR_CID, fpos) :: ar_own cx) ly S W (ms_mem ms1) mdN (ar_k cx) (ms_regs ms1)
      HAPN HRDN HPRN). }
  cbv beta. intros W2 c2 _ HQ.
  destruct HQ as (ly2 & S2 & regs2 & mem2 & md2 & Ec2 & HJ2 & HP2 & Hfr2 & Hfds2 & Hfs2 & HK2 & _ & HS2 & Hperm2 & HPOST).
  subst c2. rewrite Z.add_0_r in HJ2.
  pose proof (HPOST kbs (req_read IDX) HNKN ltac:(rewrite AN0; exact HREQ) ltac:(rewrite AN1; exact (ar_req_read_length IDX)))
    as HP3.
  cbv zeta in HP3. rewrite AN2, AN3, AN4, AN5 in HP3.
  destruct HP3 as (T10 & NL & KSo & ASo & KNo & ANo & KBo & ABo).
  rewrite G1.
  apply (ars_stage3 ly2 S2 W2 regs2 mem2 md2).
  - apply (ars_nl_step ly S W (ms_mem ms1) mdN ly2 S2 W2 mem2 md2 _ _ _ HIN HJ2 Hfr2 HS2 Hperm2 Hfds2 Hfs2 HK2).
    + rewrite HspN, HNA. lia.
    + rewrite HspN. lia.
    + rewrite EWR. intros a Ha. exact Ha.
  - exact (ars_pres _ _ (2%bv : bv 5) _ HP2 ltac:(ars_cs) G2).
  - exact (ars_pres _ _ (9%bv : bv 5) _ HP2 ltac:(ars_cs) G9).
  - exact (ars_pres _ _ (8%bv : bv 5) _ HP2 ltac:(ars_cs) G8).
  - exact (ars_pres _ _ (18%bv : bv 5) _ HP2 ltac:(ars_cs) G18).
  - exact (ars_pres _ _ (26%bv : bv 5) _ HP2 ltac:(ars_cs) G26).
  - exact (ars_pres _ _ (25%bv : bv 5) _ HP2 ltac:(ars_cs) G25).
  - exact (ars_pres _ _ (3%bv : bv 5) _ HP2 ltac:(ars_cs) G3).
  - exact (ars_pres _ _ (4%bv : bv 5) _ HP2 ltac:(ars_cs) G4).
  - exact (ars_pres _ _ (27%bv : bv 5) _ HP2 ltac:(ars_cs) G27).
  - exact T10.
  - split; [exact NL|].
    split.
    { intros Hk0 Hkn. pose proof Hkn as Hkn'. unfold ar_kn in Hkn'. unfold text_of_attr.
      destruct (a_kind (talk_attrs K0)) as [pay|] eqn:Ek.
      - first [exact (KSo pay Ek Hk0 Hkn) | exact (KSo pay eq_refl Hk0 Hkn)].
      - first [exact (KNo Ek Hk0 [] ltac:(cbn [length Z.of_nat]; lia) (proj1 (BKn Hk0 Hkn')))
              | exact (KNo eq_refl Hk0 [] ltac:(cbn [length Z.of_nat]; lia) (proj1 (BKn Hk0 Hkn')))]. }
    split.
    { intros Ha0 Han. pose proof Han as Han'. unfold ar_an in Han'. unfold text_of_attr.
      destruct (a_alias (talk_attrs K0)) as [pay|] eqn:Ea.
      - first [exact (ASo pay Ea Ha0 Han) | exact (ASo pay eq_refl Ha0 Han)].
      - first [exact (ANo Ea Ha0 [] ltac:(cbn [length Z.of_nat]; lia) (proj1 (BAn Ha0 Han')))
              | exact (ANo eq_refl Ha0 [] ltac:(cbn [length Z.of_nat]; lia) (proj1 (BAn Ha0 Han')))]. }
    split; [exact KBo | exact ABo].
Qed.

(* ==========================================================================
   4. STAGE 1 (+0x180 .. +0x1a0), the request's shadow in scope, then checked_memset, then stage 2
   ========================================================================== *)
Lemma ars_stage1 : forall ly S W (R : bvmap 5 word) m md,
  ars_inv ly S W m md ->
  getr R 2 = w64 (ar_sp1 cx) -> getr R 9 = w64 (ar_sp1 cx) -> getr R 8 = w64 (ar_sp cx) ->
  getr R 18 = w64 F -> getr R 26 = w64 F -> getr R 25 = w64 SH ->
  getr R 3 = getr (ar_regs cx) 3 -> getr R 4 = getr (ar_regs cx) 4 -> getr R 27 = getr (ar_regs cx) 27 ->
  getr R 23 = w64 IDX ->
  getr R 19 = w64 (ar_alias cx) -> getr R 20 = w64 (ar_an cx) ->
  getr R 21 = w64 (ar_kind cx) -> getr R 22 = w64 (ar_kn cx) ->
  ar_gnl_kept cx W m -> ar_bufs_nul cx W m ->
  SRr SEGS W (mkCfg (mkst R (Z_to_bv 64 (BASE + AR_CUT_SEND)) m (seg_rom SEGS)) md) (ar_post SK B cx).
Proof.
  intros ly S W R m md HI R2 R9 R8 R18 R26 R25 R3 R4 R27 R23 R19 R20 R21 R22 HGK HBN.
  pose proof HI as (HJ & Hfr & Hfs & Hperm & Hfa & _).
  destruct ars_win as (W16 & Wc & Wlo & Whi & W47 & S1lo & S1al).
  destruct ars_F as (F1 & F2 & F3 & F4 & F5 & F6).
  destruct ars_SH as (SH1 & SH2 & SH3 & SH3b & SH4 & SH5).
  pose proof asan_consts as ((C1a & C1b) & _).
  pose proof REAC_LINK_ALIAS_READ_AK_val as HK8.
  pose proof (div8_of_mul64 F F3) as (D1 & D2).
  destruct (ars_present ly S W m md HI) as [HFp HSp].
  assert (HEI : img_env VAL A_LIM (Eimg (Ereg R []))) by apply Eimg_env.
  assert (U25 : bv_unsigned (ew (Eimg (Ereg R [])) 25) = SH)
    by (apply (ars_U R 25 (25%bv : bv 5)); [reflexivity | exact R25 | lia]).
  assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg R [])) ars_ss1
    (restrict (w_H W) (mkst R (Z_to_bv 64 (BASE + AR_CUT_SEND)) m (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ars_ss1. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, ars_sh_r.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U25.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (YCbq.apresent_writable SEGS). apply HSp. unfold AR_SHN. lia.
    - cbn [pairwise_disjoint all_disjoint]. split; exact I.
    - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I]. }
  ars_run_call (paj_run_call_plain_x SK B LAWS (ar_G cx) ars_pre_g (ar_XO cx) (ar_OUT cx)) HS HJ.
  { apply awr_ok_x_cons; [|apply awr_ok_x_nil]. intros a Ha. unfold ars_sh_r in Ha.
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U25 in Ha. left.
    apply (aj_gx_awr_frame SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AR_CID fpos a HJ
      (or_introl eq_refl)).
    right. unfold in_zr. cbn [fst snd]. rewrite (Hfa AR_CID fpos). change (fs_frame_bytes AR_CID / 8) with 16.
    rewrite SH1 in Ha. unfold ar_F in Ha. unfold shadow_addr. lia. }
  intros ms1 mat1 HS1' HJ1 HF HF' HG'. cbn [ms_mem mkst] in HF, HF', HG'.
  pose proof (st_ok_restrict_mkst SEGS (w_H W) _ _ ms1 HS1' eq_refl) as Ems1. cbn [ss_pc setpc] in Ems1.
  set (md1 := with_vm_backing (m_vm_lazy md) mat1 md) in *.
  sreg HS1' (1%bv : bv 5) Q1. sreg HS1' (2%bv : bv 5) Q2. sreg HS1' (3%bv : bv 5) Q3. sreg HS1' (4%bv : bv 5) Q4.
  sreg HS1' (8%bv : bv 5) Q8. sreg HS1' (9%bv : bv 5) Q9. sreg HS1' (10%bv : bv 5) Q10.
  sreg HS1' (11%bv : bv 5) Q11. sreg HS1' (12%bv : bv 5) Q12.
  sreg HS1' (18%bv : bv 5) Q18. sreg HS1' (19%bv : bv 5) Q19. sreg HS1' (20%bv : bv 5) Q20.
  sreg HS1' (21%bv : bv 5) Q21. sreg HS1' (22%bv : bv 5) Q22. sreg HS1' (23%bv : bv 5) Q23.
  sreg HS1' (24%bv : bv 5) Q24. sreg HS1' (25%bv : bv 5) Q25. sreg HS1' (26%bv : bv 5) Q26.
  sreg HS1' (27%bv : bv 5) Q27.
  assert (G1 : getr (ms_regs ms1) 1 = Z_to_bv 64 (BASE + (AF_reac_link_alias_read + 0x1a4)))
    by (rewrite Q1; exact (codeptr_val _ (AF_reac_link_alias_read + 0x1a4) HEI)).
  assert (G2 : getr (ms_regs ms1) 2 = w64 (ar_sp1 cx)) by (rewrite Q2, (ars_atom R 2 (2%bv : bv 5) eq_refl); exact R2).
  assert (G3 : getr (ms_regs ms1) 3 = getr (ar_regs cx) 3) by (rewrite Q3, (ars_atom R 3 (3%bv : bv 5) eq_refl); exact R3).
  assert (G4 : getr (ms_regs ms1) 4 = getr (ar_regs cx) 4) by (rewrite Q4, (ars_atom R 4 (4%bv : bv 5) eq_refl); exact R4).
  assert (G8 : getr (ms_regs ms1) 8 = w64 (ar_sp cx)) by (rewrite Q8, (ars_atom R 8 (8%bv : bv 5) eq_refl); exact R8).
  assert (G9 : getr (ms_regs ms1) 9 = w64 (ar_sp1 cx)) by (rewrite Q9, (ars_atom R 9 (9%bv : bv 5) eq_refl); exact R9).
  assert (G10 : getr (ms_regs ms1) 10 = w64 (F + 44))
    by (rewrite Q10; apply (ars_atom_off R 26 (26%bv : bv 5) F 44 eq_refl R26); lia).
  assert (G11 : getr (ms_regs ms1) 11 = w64 0) by (rewrite Q11; reflexivity).
  assert (G12 : getr (ms_regs ms1) 12 = w64 20) by (rewrite Q12; reflexivity).
  assert (G18 : getr (ms_regs ms1) 18 = w64 F) by (rewrite Q18, (ars_atom R 18 (18%bv : bv 5) eq_refl); exact R18).
  assert (G19 : getr (ms_regs ms1) 19 = w64 (ar_alias cx))
    by (rewrite Q19, (ars_atom R 19 (19%bv : bv 5) eq_refl); exact R19).
  assert (G20 : getr (ms_regs ms1) 20 = w64 (ar_an cx))
    by (rewrite Q20, (ars_atom R 20 (20%bv : bv 5) eq_refl); exact R20).
  assert (G21 : getr (ms_regs ms1) 21 = w64 (ar_kind cx))
    by (rewrite Q21, (ars_atom R 21 (21%bv : bv 5) eq_refl); exact R21).
  assert (G22 : getr (ms_regs ms1) 22 = w64 (ar_kn cx))
    by (rewrite Q22, (ars_atom R 22 (22%bv : bv 5) eq_refl); exact R22).
  assert (G23 : getr (ms_regs ms1) 23 = w64 IDX) by (rewrite Q23, (ars_atom R 23 (23%bv : bv 5) eq_refl); exact R23).
  assert (G24 : getr (ms_regs ms1) 24 = w64 (F + 32))
    by (rewrite Q24; apply (ars_atom_off R 26 (26%bv : bv 5) F 32 eq_refl R26); lia).
  assert (G25 : getr (ms_regs ms1) 25 = w64 SH) by (rewrite Q25, (ars_atom R 25 (25%bv : bv 5) eq_refl); exact R25).
  assert (G26 : getr (ms_regs ms1) 26 = w64 F) by (rewrite Q26, (ars_atom R 26 (26%bv : bv 5) eq_refl); exact R26).
  assert (G27 : getr (ms_regs ms1) 27 = getr (ar_regs cx) 27)
    by (rewrite Q27, (ars_atom R 27 (27%bv : bv 5) eq_refl); exact R27).
  clear Q1 Q2 Q3 Q4 Q8 Q9 Q10 Q11 Q12 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27.
  assert (HspN : spZ (ms_regs ms1) = ar_sp1 cx) by (unfold spZ; rewrite G2; apply unsigned_lit_small; lia).
  (* the bytes the run wrote: SH + 4 .. SH + 7, now 0 *)
  assert (UN1 : forall x, 0 <= x < 2 ^ 64 -> ~ (SH + 4 <= x < SH + 8) ->
    aview SEGS (w_H W) (ms_mem ms1) x = aview SEGS (w_H W) m x).
  { intros x Hx Hn. apply (ars_frame_aview _ _ (w_H W) m (ms_mem ms1) x HF' Hx). intros (r & [<- | []] & Hr).
    unfold ars_sh_r in Hr. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite U25 in Hr. lia. }
  assert (UNs : forall x, 0 <= x < 2 ^ 64 -> ~ aside_rng (ar_lyc cx) AR_CID fpos x ->
    ~ (ar_sp cx - AK <= x < ar_sp cx) -> aview SEGS (w_H W) (ms_mem ms1) x = aview SEGS (w_H W) m x).
  { intros x Hx Hn _. apply UN1; [exact Hx|]. intros Hw. apply Hn. right; left. unfold in_zr. cbn [fst snd].
    change (fs_frame_bytes AR_CID / 8) with 16. rewrite SH1 in Hw. unfold ar_F in Hw. unfold shadow_addr. lia. }
  pose proof (st_ok_region_nth _ _ _ 0 _ HS1' eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
  assert (HSZ1 : forall i, 4 <= i < 8 -> aview SEGS (w_H W) (ms_mem ms1) (SH + i) = Some 0).
  { intros i Hi. assert (Hi' : i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
    destruct Hi' as [-> | [-> | [-> | ->]]]; apply ars_mbyte0_aview;
      match goal with |- mbyte _ _ (_ + ?o) = _ =>
        pose proof (field_of_region _ _ _ _ _ _ _ _ _ o 1%N (SLit 0) 0 HR0 U25 ltac:(ars_in) eq_refl
          ltac:(cbn; lia) ltac:(cbn; lia)) as V;
        pose proof (V 0%nat ltac:(cbn; lia)) as V0; cbn [Z.of_nat] in V0; rewrite Z.add_0_r in V0; exact V0 end. }
  assert (HI1 : ars_inv ly S W (ms_mem ms1) md1).
  { apply (ars_inv_step ly S W m md (ms_mem ms1) md1 (fun a => SH + 4 <= a < SH + 8) HI HJ1).
    - exact UN1.
    - intros a Ha. right; right. lia.
    - intros a Ha. exact (apresent_grows _ _ _ a HG' Ha).
    - subst md1. exact (proj1 (wvb_fds_fs _ _ _)).
    - subst md1. exact (proj2 (wvb_fds_fs _ _ _)). }
  pose proof (ars_gnl_keep W m (ms_mem ms1) HGK UNs) as HGK1.
  pose proof (ars_bufs_keep W m (ms_mem ms1) HBN UNs (fun a Ha => apresent_grows _ _ _ a HG' Ha)) as HBN1.
  destruct (ars_present ly S W (ms_mem ms1) md1 HI1) as [HFp1 HSp1].
  pose proof HPRE as ((_ & _ & _ & _ & _ & Hgp & Htp & _ & _ & _ & _ & _ & _ & _) & _).
  (* ---- +0x1a0: checked_memset(q + 12, 0, 20) ---- *)
  rewrite Ems1.
  eapply SRr_bind.
  { apply (aj_gx_intrin_at SK SEGS B LAWS pa_segs_low OSet (pa_sigma LS___asan_memset) AMSET (ar_G cx) (ar_XO cx)
      (ar_OUT cx) W (ms_regs ms1) (ms_mem ms1) (ar_STK cx) (ar_sp0 cx) (ar_FP cx) (ar_ly cx) (ar_S cx) (ar_W0 cx)
      (ar_mem0 cx) (ar_md0 cx) ((AR_CID, fpos) :: ar_own cx) ly S md1 (ar_k cx) (F + 44) 0 20 (getr (ms_regs ms1) 1)
      ars_pre_g HJ1 G10 G11 G12).
    - lia.
    - lia.
    - lia.
    - rewrite HspN. exact S1al.
    - rewrite HspN. unfold ESTACK. lia.
    - rewrite HspN. lia.
    - rewrite G3. exact Hgp.
    - rewrite G4. exact Htp.
    - reflexivity.
    - rewrite G1. apply ret_ok_codeptr_v; [unfold AF_reac_link_alias_read; lia | reflexivity].
    - intros a Ha. left.
      destruct (aj_gx_awr_frame SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AR_CID fpos a HJ1
        (or_introl eq_refl)) as [Haw Hno].
      { left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite (Hfa AR_CID fpos). change (fs_frame_bytes AR_CID) with 128.
        unfold ar_F in *. lia. }
      split; [exact Haw|]. split; [exact Hno|]. rewrite HspN. unfold ESTACK. lia.
    - unfold amem_range. unfold in_app in F4. destruct F4 as (_ & [Hl | (Hh & _)]); [left | right];
        unfold kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia.
    - intros x Hx. unfold shadow_of_addr. exists 0. split; [|left; reflexivity].
      replace (SHADOW_OFF + x / 8) with (SH + (x - F) / 8) by (rewrite SH1; lia).
      apply HSZ1. lia.
    - intros _ s Hs. apply ars_present_vis. apply HSp1. unfold AR_SHN. unfold shadow_addr in Hs. rewrite SH1. lia.
    - exact I. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & HB2 & HK2 & HPr2 & Hsame).
  pose proof (same_but_materialized_wvb _ _ Hsame) as Emd2.
  assert (UNm : forall x, 0 <= x < 2 ^ 64 -> ~ aside_rng (ar_lyc cx) AR_CID fpos x ->
    ~ (ar_sp cx - AK <= x < ar_sp cx) -> aview SEGS (w_H W) mem2 x = aview SEGS (w_H W) (ms_mem ms1) x).
  { intros x Hx Hn Hw. apply HK2; [exact Hx | | rewrite HspN; unfold ESTACK; lia].
    intros Hd. apply Hn. left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes AR_CID) with 128.
    unfold ar_F in *. lia. }
  assert (HI2 : ars_inv ly S W mem2 md2).
  { apply (ars_inv_step ly S W (ms_mem ms1) md1 mem2 md2
      (fun a => F + 44 <= a < F + 64 \/ ar_sp1 cx - ESTACK <= a < ar_sp1 cx) HI1 HJ2).
    - intros a Ha Hn. apply HK2; [exact Ha | intros Hd; apply Hn; left; lia | rewrite HspN; intros Hd; apply Hn; right; lia].
    - intros a [Ha | Ha]; [right; left; lia | left; unfold ESTACK in Ha; lia].
    - exact HPr2.
    - rewrite Emd2. exact (proj1 (wvb_fds_fs _ _ _)).
    - rewrite Emd2. exact (proj2 (wvb_fds_fs _ _ _)). }
  rewrite G1.
  apply (ars_stage2 ly S W regs2 mem2 md2 HI2).
  - exact (ars_pres _ _ (2%bv : bv 5) _ HP2 ltac:(ars_cs) G2).
  - exact (ars_pres _ _ (9%bv : bv 5) _ HP2 ltac:(ars_cs) G9).
  - exact (ars_pres _ _ (8%bv : bv 5) _ HP2 ltac:(ars_cs) G8).
  - exact (ars_pres _ _ (18%bv : bv 5) _ HP2 ltac:(ars_cs) G18).
  - exact (ars_pres _ _ (26%bv : bv 5) _ HP2 ltac:(ars_cs) G26).
  - exact (ars_pres _ _ (25%bv : bv 5) _ HP2 ltac:(ars_cs) G25).
  - exact (ars_pres _ _ (3%bv : bv 5) _ HP2 ltac:(ars_cs) G3).
  - exact (ars_pres _ _ (4%bv : bv 5) _ HP2 ltac:(ars_cs) G4).
  - exact (ars_pres _ _ (27%bv : bv 5) _ HP2 ltac:(ars_cs) G27).
  - exact (ars_pres _ _ (24%bv : bv 5) _ HP2 ltac:(ars_cs) G24).
  - exact (ars_pres _ _ (23%bv : bv 5) _ HP2 ltac:(ars_cs) G23).
  - exact (ars_pres _ _ (19%bv : bv 5) _ HP2 ltac:(ars_cs) G19).
  - exact (ars_pres _ _ (20%bv : bv 5) _ HP2 ltac:(ars_cs) G20).
  - exact (ars_pres _ _ (21%bv : bv 5) _ HP2 ltac:(ars_cs) G21).
  - exact (ars_pres _ _ (22%bv : bv 5) _ HP2 ltac:(ars_cs) G22).
  - exact (ars_gnl_keep W (ms_mem ms1) mem2 HGK1 UNm).
  - exact (ars_bufs_keep W (ms_mem ms1) mem2 HBN1 UNm HPr2).
  - intros i Hi. rewrite (HK2 (SH + i)); [exact (HSZ1 i Hi) | lia | lia | rewrite HspN; unfold ESTACK; lia].
  - intros i Hi. rewrite (HB2 i Hi). reflexivity.
Qed.

(* the SEND cut, from ar_base and the cut's registers *)
Lemma ars_send_at : forall ly3 S3 W3 ms3 md3,
  ms_pc_val ms3 = w64 (BASE + AR_CUT_SEND) ->
  getr (ms_regs ms3) 23 = w64 IDX ->
  getr (ms_regs ms3) 19 = w64 (ar_alias cx) -> getr (ms_regs ms3) 20 = w64 (ar_an cx) ->
  getr (ms_regs ms3) 21 = w64 (ar_kind cx) -> getr (ms_regs ms3) 22 = w64 (ar_kn cx) ->
  ar_gnl_kept cx W3 (ms_mem ms3) -> ar_bufs_nul cx W3 (ms_mem ms3) ->
  ar_base SK B cx fpos ly3 S3 W3 ms3 md3 ->
  SRr SEGS W3 (mkCfg ms3 md3) (ar_post SK B cx).
Proof using All.
  intros ly3 S3 W3 ms3 md3 Hpc R23 R19 R20 R21 R22 HGK HBN HB.
  pose proof (ars_inv_of_base ly3 S3 W3 ms3 md3 HB) as HI.
  unfold ar_base in HB. cbv zeta in HB.
  destruct HB as (Hresv & Hsvc & Hrom & Hfregs & Hfcsr & _ & _ & _ & _ & _ & _ & _ & R2 & R9 & R8 & R18 & R26 & R25 &
    R3 & R4 & R27 & _).
  rewrite (ars_ms_eta ms3 Hresv Hsvc Hfregs Hfcsr), Hpc, Hrom.
  exact (ars_stage1 ly3 S3 W3 (ms_regs ms3) (ms_mem ms3) md3 HI R2 R9 R8 R18 R26 R25 R3 R4 R27 R23 R19 R20 R21 R22
    HGK HBN).
Qed.

End c.

(* ==========================================================================
   5. THE SEND PIECE
   ========================================================================== *)
Theorem ar_send : ar_exit_obl SK B -> ar_send_obl SK B.
Proof.
  intros EXIT cx fpos ly3 S3 W3 ms3 md3 HPRE
    (sn & tab & kbs & Hpc & HNK & HIT & HSN & HN0 & HSNE & HIDX & R23 & R19 & R20 & R21 & R22 & _ & HGK & HBN & HB).
  pose proof HB as HB0. unfold ar_base in HB0. cbv zeta in HB0.
  destruct HB0 as (_ & _ & _ & _ & _ & _ & _ & Hnin & _ & _ & (S1 & W1 & mem1 & md1 & HAR1 & Hfrs1 & Eab1) & _).
  exact (ars_send_at cx fpos HPRE Hnin
    (ex_intro _ S1 (ex_intro _ W1 (ex_intro _ mem1 (ex_intro _ md1 (conj HAR1 (conj Hfrs1 Eab1))))))
    sn tab kbs HNK HIT HSN HN0 HSNE HIDX EXIT ly3 S3 W3 ms3 md3 Hpc R23 R19 R20 R21 R22 HGK HBN HB).
Qed.

End b.
End a.

Arguments ar_send {fx rc} SK {PI}.
About ar_send.
Print Assumptions ar_send.
