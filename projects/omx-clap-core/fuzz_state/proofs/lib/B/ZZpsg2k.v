(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: IMAGE B (fs.asan-ubsan) walk of parse_value 0x82fcc, stage lemmas. HEADER: see
   FSW_parse_value_holds.v (the composition into parse_value_spec k, the rule-24 line, the reuse search, the port
   sources, every pc walked and every report site). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/Prog/FSW_parse_value.v, with its module names and numbers changed; 1163 of its 1272 lines of code are new or changed and 1247 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan, image B) twin of lib/A/FSW_put_string.v at
   a working branch ca67007c8c2 (a Theorem Labs lane), and another Theorem Labs lane: same lemma names and statement shapes;
   imports point at lib/B's image files and walk kit (YB1v, YB1w, FSH_Base, FSH_Rt, FSPstat, FSH_Fn_writer,
   FSW_K, FSW_K3, FSW_ret, FSW_frame, FSW_frame3, FSW_rd, FSW_strkit and lib/B's put_string files); the
   image-agnostic FSupoison, FSupoisonU, FSupoisonStack, FSH_YC20, FSH_Gen and FSW_writer_model stay lib/A's.
   Every address, cut, branch, offset and register of put_string's own code is RE-MEASURED on image B
   (A_put_string 0x85fc8, 928 bytes; the neutral excerpt put_string.fuzz_state.asan-ubsan.s), never copied.
   rule 24: proves no function (kind: segment lemma). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/FSW_put_string.v; 138 of its 184 lines of code are new or changed and 1226 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan, image B) twin of lib/A/ZZpsg2k.v at
   a working branch ca67007c8c2 (a Theorem Labs lane), and another Theorem Labs lane: same lemma names and statement shapes;
   imports point at lib/B's image files and walk kit (YB1v, YB1w, FSH_Base, FSH_Rt, FSPstat, FSH_Fn_writer,
   FSW_K, FSW_K3, FSW_ret, FSW_frame, FSW_frame3, FSW_rd, FSW_strkit and lib/B's put_string files); the
   image-agnostic FSupoison, FSupoisonU, FSupoisonStack, FSH_YC20, FSH_Gen and FSW_writer_model stay lib/A's.
   Every address, cut, branch, offset and register of put_string's own code is RE-MEASURED on image B
   (A_put_string 0x85fc8, 928 bytes; the neutral excerpt put_string.fuzz_state.asan-ubsan.s), never copied.
   rule 24: proves no function (kind: segment lemma). *)
(* SCRATCH (piece R6 of a Theorem Labs lane): put_string's put-call HELPERS shared by SEG2 (ZZpsg2.v) and SEG3 (ZZpsg3.v),
   image B (fs.asan-ubsan). Folded by a Theorem Labs lane into FSW_put_string.v once every segment is Qed.
   - psk_chain_o: put's chain-at-o premise (FSH_Fn_writer.put_spec, its `o = spZ regs + 8 \/ ...` clause) at a put call
     whose machine sp is put_string's re-aligned sp1, from put_string_spec's own clause at the ENTRY sp: entry arm 1
     (o right above put_string's frame) becomes arm 2 at sp1, its second word being put_string's saved ra at s0 - 8.
   - psk_fp_rel: FSW_put_string.ps_put_call's four-arm footprint relation for the callee's buffer wbuf_fp buf1 cap1,
     against put_string's own FP (FS_PSTAT_FP ++ wbuf_fp buf0 cap0 at the entry), from the bswap the walk composes
     from the entry and AR at the call (the live block list has no repeat: ZZpsmodel.psm_ablocks_nodup).
   - psk_wout_blk: the two facts of wout_ok those take (the buffer's block is live; cap = 0 -> buf = 0). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v FSH_Base FSH_Rt FSPstat FSW_K FSW_put_string ZZpssep ZZpsmodel.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require
FSH_Fn_writer FSW_rd.
From OSSVerify.omx_clap_core.fuzz_state.images Require AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================= closed arithmetic and reader facts ================= *)
(* eight readable bytes make a word *)
Lemma psk_rdword_some : forall (rd : reader) a, (forall k, 0 <= k < 8 -> rd (a + k) <> None) ->
  exists v, rdword rd a = Some v.
Proof.
intros rd a H. unfold rdword.
destruct (rd a) as [b0|] eqn:E0; [|exfalso; apply (H 0); [lia | rewrite Z.add_0_r; exact E0]].
destruct (rd (a + 1)) as [b1|] eqn:E1; [|exfalso; exact (H 1 ltac:(lia) E1)].
destruct (rd (a + 2)) as [b2|] eqn:E2; [|exfalso; exact (H 2 ltac:(lia) E2)].
destruct (rd (a + 3)) as [b3|] eqn:E3; [|exfalso; exact (H 3 ltac:(lia) E3)].
destruct (rd (a + 4)) as [b4|] eqn:E4; [|exfalso; exact (H 4 ltac:(lia) E4)].
destruct (rd (a + 5)) as [b5|] eqn:E5; [|exfalso; exact (H 5 ltac:(lia) E5)].
destruct (rd (a + 6)) as [b6|] eqn:E6; [|exfalso; exact (H 6 ltac:(lia) E6)].
destruct (rd (a + 7)) as [b7|] eqn:E7; [|exfalso; exact (H 7 ltac:(lia) E7)].
eexists. reflexivity.
Qed.

Lemma psk_inFP_app : forall l1 l2 a, inFP (l1 ++ l2) a -> inFP l1 a \/ inFP l2 a.
Proof.
intros l1 l2 a (r & Hr & Ha). apply in_app_or in Hr as [Hr | Hr]; [left | right]; exists r; split; assumption.
Qed.
Lemma psk_inFP_r : forall l1 l2 a, inFP l2 a -> inFP (l1 ++ l2) a.
Proof. intros l1 l2 a (r & Hr & Ha). exists r. split; [apply in_or_app; right; exact Hr | exact Ha]. Qed.
Lemma psk_inFP_l : forall l1 l2 a, inFP l1 a -> inFP (l1 ++ l2) a.
Proof. intros l1 l2 a (r & Hr & Ha). exists r. split; [apply in_or_app; left; exact Hr | exact Ha]. Qed.

Lemma psk_blk_rng : forall buf cap a, buf - HEAD <= a < buf + cap ->
  buf - HEAD <= a < buf - HEAD + req_size (cap + HEAD).
Proof. intros buf cap a H. pose proof (pss_req_ge (cap + HEAD)). unfold HEAD in *. lia. Qed.

Lemma psk_head_eq : forall b1 c1 b0 c0, (b1 - HEAD, c1 + HEAD) = (b0 - HEAD, c0 + HEAD) -> b1 = b0 /\ c1 = c0.
Proof. intros b1 c1 b0 c0 E. injection E as E1 E2. unfold HEAD in *. split; lia. Qed.

(* ================= (c) put's chain-at-o premise at the re-aligned sp ================= *)
Section C0. Context {rc : YM05.RunCeil}.
Lemma psk_chain_o : forall (rd rdc : reader) (regs regsc : bvmap 5 word) o,
  (o = spZ regs + 8 /\ raZ regs < alloc_ceiling \/
   spZ regs + 16 <= o /\ exists ra nfp, rdword rd (o - 8) = Some ra /\ rdword rd (o - 16) = Some nfp /\
     (ra < 4096 \/ nfp < alloc_ceiling)) ->
  spZ regsc + 16 <= spZ regs ->
  (forall a, spZ regs <= a < o -> rdc a = rd a) ->
  (forall a, spZ regs <= a < spZ regs + 8 -> rdc a <> None) ->
  rdword rdc (spZ regs - 8) = Some (raZ regs) ->
  (o = spZ regsc + 8 /\ raZ regsc < alloc_ceiling \/
   spZ regsc + 16 <= o /\ exists ra nfp, rdword rdc (o - 8) = Some ra /\ rdword rdc (o - 16) = Some nfp /\
     (ra < 4096 \/ nfp < alloc_ceiling)).
Proof.
intros rd rdc regs regsc o Hch Hsp Hag Hpr Hra.
destruct Hch as [(Ho & Hra0) | (Ho & ra & nfp & R8 & R16 & Hor)].
- right. split; [lia|].
  destruct (psk_rdword_some rdc (spZ regs) (fun k Hk => Hpr (spZ regs + k) ltac:(lia))) as (v & Hv).
  exists v, (raZ regs).
  split; [replace (o - 8) with (spZ regs) by lia; exact Hv|].
  split; [replace (o - 16) with (spZ regs - 8) by lia; exact Hra | right; exact Hra0].
- right. split; [lia|]. exists ra, nfp.
  split; [rewrite (rdword_ext rd rdc (o - 8)); [exact R8 | intros k Hk; apply Hag; lia]|].
  split; [rewrite (rdword_ext rd rdc (o - 16)); [exact R16 | intros k Hk; apply Hag; lia] | exact Hor].
Qed.
End C0.

(* ================= (d) the four-arm footprint relation for a later put's buffer ================= *)
Section K. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

Lemma psk_wout_blk : forall ly S (W : world tfibsegs) mem o buf cap failed (text : list Z),
  FSH_Fn_writer.wout_ok B tfibsegs ly S W mem o buf cap failed text ->
  (cap <> 0 -> In (buf - HEAD, cap + HEAD) (ablocks B ly S)) /\ (cap = 0 -> buf = 0).
Proof.
intros ly S W mem o buf cap failed text HOUT. unfold FSH_Fn_writer.wout_ok in HOUT.
destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [(E0 & Eb & _) | ((j & Hj & Ec) & (Hbl & _) & _)]).
- split; [intros Hc; exfalso; exact (Hc E0) | intros _; exact Eb].
- pose proof (Z.pow_pos_nonneg 2 j ltac:(lia) (proj1 Hj)) as Hp.
  split; [intros _; exact Hbl | intros Hc; exfalso; lia].
Qed.

Lemma psk_fp_rel : forall ly S lyc Sc (Wc : world tfibsegs) memc mdc buf0 cap0 buf1 cap1 own a,
  AR tfibsegs B lyc Sc Wc memc mdc ->
  FSH_Fn_writer.bswap (ablocks B ly S) (ablocks B lyc Sc) buf0 buf1 cap0 cap1 ->
  (cap1 <> 0 -> In (buf1 - HEAD, cap1 + HEAD) (ablocks B lyc Sc)) ->
  inFP (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf1 cap1) a ->
  (inFP (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf0 cap0) a /\
     exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
  in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a \/
  (inFP (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf0 cap0) a /\ in_img tfibsegs a) \/
  in_frames lyc own a.
Proof.
intros ly S lyc Sc Wc memc mdc buf0 cap0 buf1 cap1 own a HAR Hsw Hblk1 Hfp.
apply psk_inFP_app in Hfp as [Hp | Hb].
{ right; right; left. split; [exact (psk_inFP_l _ _ a Hp)|]. apply pss_pstat_img. exact Hp. }
unfold FSH_Fn_writer.wbuf_fp in Hb. destruct (Z.eqb_spec cap1 0) as [E1 | E1].
{ exfalso. exact (inFP_nil a Hb). }
destruct Hb as (r & [<- | []] & Ha). cbn [fst snd] in Ha.
pose proof (Hblk1 E1) as Hin1.
pose proof (psm_ablocks_nodup tfibsegs B lyc Sc Wc memc mdc HAR) as HND.
assert (HR : buf1 - HEAD <= a < buf1 - HEAD + req_size (cap1 + HEAD)) by exact (psk_blk_rng buf1 cap1 a Ha).
(* the old buffer's own range: when the call kept the block, a lies in put_string's FP *)
assert (OLD : buf1 = buf0 -> cap1 = cap0 ->
              inFP (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf0 cap0) a /\
              exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n).
{ intros -> ->. split; [|exists (buf0 - HEAD), (cap0 + HEAD); split; [exact Hin1 | exact HR]].
  apply psk_inFP_r. unfold FSH_Fn_writer.wbuf_fp. destruct (Z.eqb_spec cap0 0) as [E0 | _]; [exfalso; exact (E1 E0)|].
  exists (buf0 - HEAD, buf0 + cap0). split; [left; reflexivity | cbn [fst snd]; exact Ha]. }
(* otherwise the new block is no block of the entry: a temporary block *)
assert (TMP : ~ In (buf1 - HEAD, cap1 + HEAD) (ablocks B ly S) ->
              in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a).
{ intros Hn. exists (buf1 - HEAD), (cap1 + HEAD). split; [exact Hin1|]. split; [exact Hn | exact HR]. }
destruct Hsw as [(Eb & Ec & EA) | [(Ec0 & C1 & C2 & EA & EC) | (A1 & A2 & C1 & C2 & EA & EA' & EC)]].
- left. exact (OLD Eb Ec).
- right; left. apply TMP. rewrite <- EC. apply NoDup_remove_2. rewrite <- EA. exact HND.
- destruct (Z.eq_dec buf1 buf0) as [Eb | Eb]; [destruct (Z.eq_dec cap1 cap0) as [Ec | Ec]|].
  + left. exact (OLD Eb Ec).
  + right; left. apply TMP. rewrite EA. intros Hin. apply in_app_or in Hin as [Hin | [Hh | Hin]].
    * apply (NoDup_remove_2 C1 C2 (buf1 - HEAD, cap1 + HEAD)); [rewrite <- EA'; exact HND|].
      rewrite EC. apply in_or_app. left. exact Hin.
    * exact (Ec (proj2 (psk_head_eq _ _ _ _ (eq_sym Hh)))).
    * apply (NoDup_remove_2 C1 C2 (buf1 - HEAD, cap1 + HEAD)); [rewrite <- EA'; exact HND|].
      rewrite EC. apply in_or_app. right. exact Hin.
  + right; left. apply TMP. rewrite EA. intros Hin. apply in_app_or in Hin as [Hin | [Hh | Hin]].
    * apply (NoDup_remove_2 C1 C2 (buf1 - HEAD, cap1 + HEAD)); [rewrite <- EA'; exact HND|].
      rewrite EC. apply in_or_app. left. exact Hin.
    * exact (Eb (proj1 (psk_head_eq _ _ _ _ (eq_sym Hh)))).
    * apply (NoDup_remove_2 C1 C2 (buf1 - HEAD, cap1 + HEAD)); [rewrite <- EA'; exact HND|].
      rewrite EC. apply in_or_app. right. exact Hin.
Qed.

(* ================= (e) ARU at the entry, from fpreU ================= *)
Lemma psk_aru_pre : forall STK ly S U (W : world tfibsegs) regs mem md ch,
  fpreU tfibsegs B STK ly S U W regs mem md ch -> ARU tfibsegs B ly S U W mem md.
Proof.
intros STK ly S U W regs mem md ch (((HAR & _) & HO & HP) & _).
split; [exact HAR | split; [exact HO | exact HP]].
Qed.

(* ================= (f) the read-only view at a put return, from the ENTRY ================= *)
(* FSW_rd.arodata_kept_own over the walk's journal from the entry (put_string's FP = the allocator statics and the
   entry buffer): no read-only byte is in that FP (the statics lie in the writable data segment, above FS_RHI; a live
   block is no image byte), and the FP does not hold address 0 (the sink is closed) *)
Lemma psk_pstat_not_ro : forall a, inFP FS_PSTAT_FP a -> ~ in_roP tfibsegs FS_RLO FS_RHI a.
Proof.
intros a HP Hro. pose proof (pss_pstat_rng a HP) as [H1 H2].
destruct Hro as [(sg & Hin & Hw & Hr) | Hr]; [|unfold FS_RLO, FS_RHI in Hr; lia].
change tfibsegs with [AsanUbsan.AsanUbsan_segment_000; AsanUbsan.AsanUbsan_segment_001; AsanUbsan.AsanUbsan_segment_002; AsanUbsan.AsanUbsan_segment_003]
  in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hw, Hr; try discriminate Hw; lia.
Qed.

Lemma psk_arodata_ret : forall STK jt ly S U (W : world tfibsegs) mem md own ly' S' U' (W' : world tfibsegs) mem' md' k
    buf cap,
  ajournal tfibsegs B STK jt (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf cap) ly S W (unpoison U mem) md own
    ly' S' W' (unpoison U' mem') md' k ->
  ARU tfibsegs B ly S U W mem md -> ARU tfibsegs B ly' S' U' W' mem' md' ->
  (cap <> 0 -> In (buf - HEAD, cap + HEAD) (ablocks B ly S)) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') mem').
Proof.
intros STK jt ly S U W mem md own ly' S' U' W' mem' md' k buf cap HJ HU HU' Hblk HR.
pose proof HU' as (_ & HO' & HP').
pose proof (AR_laws_ok tfibsegs B) as LAWS.
apply (FSW_rd.arodata_kept_own B STK jt _ ly S U W mem md own ly' S' U' W' mem' md' k HJ HU HO' HP');
  [ | | exact HR].
- intros (r & Hr & Ha). apply in_app_or in Hr as [Hr | Hr].
  + pose proof (pss_pstat_rng 0 (ex_intro _ r (conj Hr Ha))) as X. lia.
  + unfold FSH_Fn_writer.wbuf_fp in Hr. destruct (Z.eqb_spec cap 0) as [E | E]; [destruct Hr|].
    destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md _ _ (proj1 HU) (Hblk E)) as (_ & H4 & _).
    unfold HEAD in *. lia.
- intros a Hro Hfp. apply psk_inFP_app in Hfp as [Hp | Hb]; [exact (psk_pstat_not_ro a Hp Hro)|].
  unfold FSH_Fn_writer.wbuf_fp in Hb. destruct (Z.eqb_spec cap 0) as [E | E]; [exact (inFP_nil a Hb)|].
  destruct Hb as (r & [<- | []] & Ha). cbn [fst snd] in Ha.
  exact (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md _ _ a (proj1 HU) (Hblk E) (psk_blk_rng buf cap a Ha)
           (FSW_rd.fsw_roP_img a Hro)).
Qed.

End K.
