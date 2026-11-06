(* check_round_trip 0x81a9c (fuzz_state.c:278-314 with round_trip_document fs.c:229-264 inlined), fs.asan (image
   tfibsegs, the pinned fuzz_state.asan sha256 64b53ff86172bb07f93f146e67b81a0354bca88e0a580e93fb1da01406fb76e0): the ASan
   walk of FSH_Fn_crt.v check_round_trip_spec, LANE B1 = segments 10-13, crt_INV_82068 -> crt_INV_8212c (the second
   decode 0x82074, bcmp 0x82098, pj_object 0x82120 and 0x82128), with the class-3 fake frame live (own = [(3, pos)]);
   plus the three pj_set FP site lemmas of segments 15 / 17 / 19 (lane B2 uses them).
   rule 24: proves no function (kind: segment lemmas of check_round_trip's walk, PORTED from a working branch
   d25a984c903 proofs/omx-clap-core/fuzz_state/lib/A/Prog/check_round_trip_sd3.v (the stretch 0x82078 .. 0x8213c:
   crt_cmp_seg :239, crt_objs_seg :371, crt_seg3 :562, crt_obj_hdr :693; stage cuts St3 :260 / St4 :315 of
   check_round_trip_stdefs.v); the function's reuse search is crt-lane-head.md's rule-24 line (checker a Theorem Labs lane
   04:26Z). The step forms are the S0 statement's (crt_from), the call crossing FSH_crt_site.crt_seg_call.
   Ported from (first draft, kept as the record): CHECKER VERDICT a Theorem Labs lane (22:47Z) CONFIRM "none for build A, by
   name or address: the released `check_round_trip` proofs are plain/ubsan only, 0x138ac/0x139ac" - superseded by the
   exact ASan proof d25a984c903 found at 04:26Z, which this file now ports. *)
(*

   The ten segments (MEASURED, capstone 5.0.7 over the pinned fs.asan):
     10  0x82068..0x82074  `bnez a0` (strcmp's answer) to the trap arm 0x824b8; decode (s2 = encode's text,
                           s11 = &n = F + 0x1c0): preset_base64_decode 0x8481c, lenp in crt's FAKE frame
     11  0x82078..0x82098  `beqz a0` (decode's answer) to 0x824b8; s9 := the decoded block; `ld a0, 0(s11)` (n);
                           `bne a0, s4` to 0x824b8 (n = |bs|); `beqz s4` SKIPS the bcmp to 0x820a0 when |bs| = 0;
                           bcmp (s9, s5 = bd, s4 = |bs|) through the thunk 0x42668
     12  0x8209c..0x82120  `bnez a0` (bcmp's answer) to 0x824b8; 29 `sb zero, k(s3)`: the shadow of the five frame
                           objects doc / state / v / back / n0 made addressable (lifetime start); s11 := ld 0x20(s1)
                           = F + 0x1a0; `sd zero, 0(s11)`; pj_object (doc = s10 = F + 0x20)
     13  0x82124..0x82128  pj_object (state = s7 = F + 0x80)
     14  0x8212c..0x82138  pj_string (v = s6 = F + 0xe0, "org.openmixer.preset/2" 0x20ea0)
     15  0x8213c..0x82150  pj_set (doc, "format" 0x20ee0, v)
     16  0x82154..0x82164  pj_string (v, "state" 0x20f00)
     17  0x82168..0x8217c  pj_set (doc, "carries" 0x20f20, v)
     18  0x82180..0x82190  pj_string (v, "base64" 0x20f40)
     19  0x82194..0x821a8  pj_set (state, "encoding" 0x20f60, v)
   F = frame_addr lyc 3 pos, the class-3 fake frame (fs_frame_bytes 3 = 512, measured shadow poke 0x81b80-0x81c74):
   doc [0x20, 0x58), state [0x80, 0xb8), v [0xe0, 0x118), back [0x140, 0x178), the two size_t at 0x1a0 and 0x1c0.

   OBLIGATION at each pj_set call (a Theorem Labs lane 22:56Z, the reader's audited awr_byte fake-frame arm): the FP passed to
   pj_set (and through it to grow) covers ONLY the object's bytes inside crt's class-3 frame and its shadow. Stated and
   proved once per site: crt_pjset_fp_ok_150, crt_pjset_fp_ok_17c, crt_pjset_fp_ok_1a8 (crt_pjset_fp_at below). The
   callee store sites they protect: pj_set 0x83a10 / 0x8394c, grow 0x83b08 / 0x83b54 / 0x83b64. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSH_Fn_reader FSH_Fn_writer
FSH_Fn_crt FSW_crt_tbl FSW_rres FSW_frame FSW_frame3 FSW_strkit FSW_rd FSH_crt_base FSH_crt_site FSH_crt_cstr.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require AF0x FSH_crt_segD.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpecFacts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.



(* ================= the class-3 frame's objects (offsets from F, MEASURED 0x81f80-0x81fa0) ================= *)
Definition crtB_DOC : Z := 0x20.
Definition crtB_STATE : Z := 0x80.
Definition crtB_V : Z := 0xe0.
Definition crtB_BACK : Z := 0x140.
Definition crtB_N0 : Z := 0x1a0.
Definition crtB_LENP : Z := 0x1c0.


Section fp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* ---- the FP of a pj_set call from check_round_trip, against crt's class-3 frame ----
   pj_set_spec's footprint at obj o and val w is [(o + 24, o + 56); (w, w + 56)] ++ ablocks_fp (rd_hblocks Dold0) ++
   FS_PSTAT_FP (FSH_Fn_reader.v pj_set_spec). ajournal's frame clause (YCbq.v ajournal) keeps every byte of a live frame
   AND of its shadow that is not in the callee's FP. crt_pjset_fp_at names the conjunct a call site must prove: inside
   crt's frame [F, F + 512) and its shadow [shadow_addr F, shadow_addr F + 64) that FP covers ONLY obj's bytes [24, 56)
   and val's 56 bytes, and both object ranges are frame bytes, i.e. the own-frame arm `in_frames ly [(3, pos)]` of the
   after-call FP relation. The proof is the base's FSH_crt_base.crt_pjset_fp_gen (one copy for the six sites). *)
Definition crt_pjset_fp_at (ly : alayout) (pos : Z) (Dold0 : list (Z * Z)) (oo ow : Z) : Prop :=
  let F := frame_addr ly 3 pos in
  (forall a, inFP ([(F + oo + 24, F + oo + 56); (F + ow, F + ow + 56)] ++ ablocks_fp (rd_hblocks Dold0) ++ FS_PSTAT_FP) a ->
     in_zr a (frame_rng ly (3, pos)) \/ in_zr a (shadow_addr F, fs_frame_bytes 3 / 8) ->
     F + oo + 24 <= a < F + oo + 56 \/ F + ow <= a < F + ow + 56) /\
  (forall a, F + oo + 24 <= a < F + oo + 56 \/ F + ow <= a < F + ow + 56 -> in_frames ly [(3, pos)] a).


(* the three pj_set sites of this group: obj = doc (s10) twice, then state (s7); val = v (s6) each time *)
Lemma crt_pjset_fp_ok_150 : forall ly S W mem md pos Dold0,
  AR tfibsegs B ly S W mem md -> In (3, pos) (frames S) ->
  (forall bk, In bk (rd_hblocks Dold0) -> In bk (ablocks B ly S)) ->
  crt_pjset_fp_at ly pos Dold0 crtB_DOC crtB_V.
Proof.
intros ly S W mem md pos Dold0 HAR Hin Hblk.
exact (crt_pjset_fp_gen B ly S W mem md pos Dold0 crtB_DOC crtB_V HAR Hin Hblk
  ltac:(unfold crtB_DOC; lia) ltac:(unfold crtB_DOC; lia) ltac:(unfold crtB_V; lia) ltac:(unfold crtB_V; lia)).
Qed.
Lemma crt_pjset_fp_ok_17c : forall ly S W mem md pos Dold0,
  AR tfibsegs B ly S W mem md -> In (3, pos) (frames S) ->
  (forall bk, In bk (rd_hblocks Dold0) -> In bk (ablocks B ly S)) ->
  crt_pjset_fp_at ly pos Dold0 crtB_DOC crtB_V.
Proof.
intros ly S W mem md pos Dold0 HAR Hin Hblk.
exact (crt_pjset_fp_gen B ly S W mem md pos Dold0 crtB_DOC crtB_V HAR Hin Hblk
  ltac:(unfold crtB_DOC; lia) ltac:(unfold crtB_DOC; lia) ltac:(unfold crtB_V; lia) ltac:(unfold crtB_V; lia)).
Qed.
Lemma crt_pjset_fp_ok_1a8 : forall ly S W mem md pos Dold0,
  AR tfibsegs B ly S W mem md -> In (3, pos) (frames S) ->
  (forall bk, In bk (rd_hblocks Dold0) -> In bk (ablocks B ly S)) ->
  crt_pjset_fp_at ly pos Dold0 crtB_STATE crtB_V.
Proof.
intros ly S W mem md pos Dold0 HAR Hin Hblk.
exact (crt_pjset_fp_gen B ly S W mem md pos Dold0 crtB_STATE crtB_V HAR Hin Hblk
  ltac:(unfold crtB_STATE; lia) ltac:(unfold crtB_STATE; lia) ltac:(unfold crtB_V; lia) ltac:(unfold crtB_V; lia)).
Qed.
End fp.

(* ================= the walk's own steps (segment group B1) =================
   The call crossing is FSH_crt_site.crt_seg_call / crt_seg_call_br (generic post; a Theorem Labs lane's text, whose helpers came
   from this file's crtB_ss2 / crtB_mkst / crtB_sb), the keeps across a callee journal are FSH_crt_site.crt_keep_*
   (from this file), the call-site precondition is crt_site_pre. What stays here is segment B1's own. *)
Section walk. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* the sink head: a Section variable, passed explicitly wherever a statement takes one (S0 removed the inferable
   instance; ENTRY instantiates it, build A's is AE2k.tfib_sink_head) *)
Variable SK : YI16.sink_head.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* ================= the boundary invariant's data facts across a callee, on the MACHINE's memories =================
   The data predicates read memory two ways: by mbyte (val_mem, garr8 = zbytes_at, fs_rblock's head word), which an
   aview equality carries directly (YCbq.mbyte_of_aview), and pointwise on the restricted memory (PjStruct's pj_node /
   pj_hdr), which an aview equality carries at a non-image byte (YCbq.seg_rom_none: there mbyte is the raw read). *)
Lemma crtB_mres_of_aview : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_img tfibsegs a ->
  aview tfibsegs H' m' a = aview tfibsegs H m a -> mrestrict H' m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a).
Proof.
intros H H' m m' a Ha Hn E. pose proof (mbyte_of_aview tfibsegs H H' m m' a E) as M.
unfold mbyte in M. rewrite (seg_rom_none tfibsegs a Ha Hn) in M.
destruct (mrestrict H' m' (Z_to_bv 64 a)), (mrestrict H m (Z_to_bv 64 a)); congruence.
Qed.
Lemma crtB_val_mem_keep : forall (H H' : word -> bool) (m m' : word -> option byte) a (n : nat) v,
  (forall i, 0 <= i < Z.of_nat n -> aview tfibsegs H' m' (a + i) = aview tfibsegs H m (a + i)) ->
  val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v K V k Hk.
rewrite (mbyte_of_aview tfibsegs H H' m m' (a + Z.of_nat k) (K (Z.of_nat k) ltac:(lia))). exact (V k Hk).
Qed.
Lemma crtB_garr8_keep : forall (H H' : word -> bool) (m m' : word -> option byte) a l,
  (forall i, 0 <= i < Z.of_nat (length l) -> aview tfibsegs H' m' (a + i) = aview tfibsegs H m (a + i)) ->
  garr8 tfibsegs (mrestrict H m) a l -> garr8 tfibsegs (mrestrict H' m') a l.
Proof.
intros H H' m m' a l K G j Hj. destruct (G j Hj) as (V & Hb). split; [|exact Hb].
apply (crtB_val_mem_keep H H' m m' _ 1 _); [|exact V].
intros i Hi. assert (i = 0) as -> by lia. rewrite Z.add_0_r. apply K. lia.
Qed.
(* a frame byte outside the callee's footprint, pointwise on the restricted memories *)
Lemma crtB_mres_keep_frm : forall lyc Sc Uc (W : world tfibsegs) memC mdC ly' S' U' (W' : world tfibsegs) mem' md'
  STKc sp1 FPc kc cid pos a,
  ARU tfibsegs B lyc Sc Uc W memC mdC -> ARU tfibsegs B ly' S' U' W' mem' md' ->
  @ajournal rc SK tfibsegs B STKc sp1 FPc lyc Sc W (unpoison Uc memC) mdC [] ly' S' W' (unpoison U' mem') md' kc ->
  In (cid, pos) (frames Sc) -> frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid ->
  ~ inFP FPc a ->
  mrestrict (w_H W') mem' (Z_to_bv 64 a) = mrestrict (w_H W) memC (Z_to_bv 64 a).
Proof.
intros lyc Sc Uc W memC mdC ly' S' U' W' mem' md' STKc sp1 FPc kc cid pos a HARU HARU' HJ Hin Ha Hnf.
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARU) as HAR.
destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ cid pos HAR Hin) as (H4096 & Hceil & _).
pose proof (@alloc_ceiling_lt rc) as HC47. change (2 ^ 47) with 140737488355328 in HC47.
apply crtB_mres_of_aview.
- change (2 ^ 64) with 18446744073709551616. lia.
- exact (frm_img tfibsegs B LAWS _ _ _ _ _ cid pos a HAR Hin Ha).
- apply (crt_keep_frm SK B lyc Sc Uc W memC mdC ly' S' U' W' mem' md' STKc sp1 FPc kc cid pos a HARU HARU' HJ Hin);
    [unfold in_zr, frame_rng; cbn [fst snd]; lia | exact Hnf].
Qed.
(* the addressability of a stretch of a live frame whose shadow lies outside the callee's footprint *)
Lemma crtB_RA_keep_frm : forall lyc Sc Uc (W : world tfibsegs) memC mdC ly' S' U' (W' : world tfibsegs) mem' md'
  STKc sp1 FPc kc cid pos p n,
  ARU tfibsegs B lyc Sc Uc W memC mdC -> ARU tfibsegs B ly' S' U' W' mem' md' ->
  @ajournal rc SK tfibsegs B STKc sp1 FPc lyc Sc W (unpoison Uc memC) mdC [] ly' S' W' (unpoison U' mem') md' kc ->
  In (cid, pos) (frames Sc) -> frame_addr lyc cid pos mod 8 = 0 -> fs_frame_bytes cid mod 8 = 0 ->
  frame_addr lyc cid pos <= p -> p + n <= frame_addr lyc cid pos + fs_frame_bytes cid ->
  (forall x, p <= x < p + n -> ~ inFP FPc (shadow_addr x)) ->
  range_addressable (aview tfibsegs (w_H W) memC) SHADOW_OFF p n ->
  range_addressable (aview tfibsegs (w_H W') mem') SHADOW_OFF p n.
Proof.
intros lyc Sc Uc W memC mdC ly' S' U' W' mem' md' STKc sp1 FPc kc cid pos p n HARU HARU' HJ Hin H8 H8b Hlo Hhi Hnf.
apply range_addressable_agree. intros x Hx.
set (F := frame_addr lyc cid pos) in *.
assert (E : shadow_of_addr SHADOW_OFF x = shadow_addr F + (x - F) / 8).
{ unfold shadow_of_addr, shadow_addr. Z.div_mod_to_equations. lia. }
assert (Ho : 0 <= (x - F) / 8 < fs_frame_bytes cid / 8) by (Z.div_mod_to_equations; lia).
rewrite E. apply (crt_keep_fsh SK B lyc Sc Uc W memC mdC ly' S' U' W' mem' md' STKc sp1 FPc kc cid pos _ HARU HARU' HJ Hin Ho).
fold F. rewrite <- E. exact (Hnf x Hx).
Qed.

(* the empty object pj_object leaves: its header is type 6 with str = kids = keys = n = cap = 0 (PjStruct.pj_node's JObj
   arm with no blocks forces cap = 0, hence kids = keys = 0; n = |[]|). Port of d25a984c903 sd3 crt_obj_hdr :693. *)
Lemma crtB_obj0_hdr : forall ly S (W : world tfibsegs) m v,
  rtree tfibsegs B ly S W m v (PjTree.JObj []) [] ->
  exists num, PjStruct.pj_hdr tfibsegs (mrestrict (w_H W) m) v 6 num 0 0 0 0 0.
Proof.
intros ly S W m v (Hn & _ & _). cbn [PjStruct.pj_node] in Hn.
destruct Hn as (_ & _ & num & str & kids & keys & n & cap & Hh & Hs & Hnn & Hle & Hk & Di & ED & _).
cbn [length Z.of_nat] in Hnn. subst str n.
destruct Hk as [(-> & -> & ->) | (Hc & _ & _)].
- exists num. exact Hh.
- exfalso. rewrite (proj2 (Z.eqb_neq cap 0) ltac:(lia)) in ED. discriminate ED.
Qed.
(* the empty object carried across a call that keeps its 56 bytes, pointwise on the restricted memories *)
Lemma crtB_obj0_keep : forall ly S (W : world tfibsegs) m ly' S' (W' : world tfibsegs) m' v,
  (forall x : word, v <= bv_unsigned x < v + 56 -> mrestrict (w_H W') m' x = mrestrict (w_H W) m x) ->
  rtree tfibsegs B ly S W m v (PjTree.JObj []) [] -> rtree tfibsegs B ly' S' W' m' v (PjTree.JObj []) [].
Proof.
intros ly S W m ly' S' W' m' v K (Hn & _ & _). split; [|split].
- apply (PjStruct.pj_node_frame tfibsegs (PjTree.JObj []) _ _ _ _ v [] Hn); [intros a k []|].
  intros x [Hx | (b & [] & _)]. exact (K x Hx).
- intros a k [].
- intros a [].
Qed.
Lemma crtB_hdr_keep : forall (W W' : world tfibsegs) m m' v num,
  (forall x : word, v <= bv_unsigned x < v + 56 -> mrestrict (w_H W') m' x = mrestrict (w_H W) m x) ->
  PjStruct.pj_hdr tfibsegs (mrestrict (w_H W) m) v 6 num 0 0 0 0 0 ->
  PjStruct.pj_hdr tfibsegs (mrestrict (w_H W') m') v 6 num 0 0 0 0 0.
Proof. intros W W' m m' v num K H. exact (PjStruct.pj_hdr_eq tfibsegs _ _ v 6 num 0 0 0 0 0 H K). Qed.
End walk.

(* ================= segment 13: 0x82124 -> pj_object (state = s7 = F + 0x80) -> 0x8212c =================
   Port of d25a984c903 sd3 crt_objs_seg's second half (:371-557): `mv a0, s7; jal pj_object`. The boundary at 0x82124
   is crt_INV_8212c without the state object (only its placement, pobj). *)
Definition crtB_sc13 : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL A_pj_object (crt_ss2 0x82124)).
Lemma crtB_run13 : sym_run_toN tfibsegs crt_tbl FUEL A_pj_object (crt_ss2 0x82124) = (crtB_sc13, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtB_site13 : crt_csite crtB_sc13 A_pj_object 0x8212c /\ sr_get (ss_regs crtB_sc13) 10%bv = SOff 23 0 /\
  crt_ssave crtB_sc13.
Proof.
split; [unfold crt_csite; repeat split; vm_compute; reflexivity|].
split; [vm_compute; reflexivity | apply crt_ssave_dec; vm_compute; reflexivity].
Qed.

Section inv13. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Definition crtB_INV_82124 : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  let mem := ms_mem ms3 in let F := crt_F cx in let len := Z.of_nat (length (c_bs cx)) in
  let tb2 := WriterSpec.b64_enc (c_bs cx) in
  ew E 18 = Z_to_bv 64 (c_text cx) /\ ew E 20 = Z_to_bv 64 len /\
  ew E 21 = Z_to_bv 64 (c_bd cx) /\ ew E 22 = Z_to_bv 64 (F + 0xe0) /\ ew E 23 = Z_to_bv 64 (F + 0x80) /\
  ew E 26 = Z_to_bv 64 (F + 0x20) /\ ew E 27 = Z_to_bv 64 (F + 0x1a0) /\
  (exists same nsame dec live peak cnt,
     ew E 24 = Z_to_bv 64 same /\ ew E 25 = Z_to_bv 64 dec /\
     Permutation (ablocks B ly3 S3)
       (ablocks B (c_ly cx) (c_S cx) ++
        [(c_text cx - HEAD, FSH_Fn_writer.enc_size len + HEAD); (c_want cx, FSH_Fn_writer.enc_size len);
         (same, nsame); (dec - HEAD, FSH_Fn_writer.dec_size tb2 + HEAD)]) /\
     Permutation U3 (c_U cx ++ [(c_text cx - HEAD, HEAD); (dec - HEAD, HEAD)]) /\
     FSupoisonU.fs_heads B ly3 S3 U3 /\
     fs_rblock tfibsegs B ly3 S3 W3 mem (c_text cx) (FSH_Fn_writer.enc_size len) /\
     zbytes_at tfibsegs W3 mem (c_text cx) (tb2 ++ [0]) /\ cstr_ok tfibsegs W3 mem (c_text cx) tb2 /\
     fs_rblock tfibsegs B ly3 S3 W3 mem dec (FSH_Fn_writer.dec_size tb2) /\
     zbytes_at tfibsegs W3 mem dec (c_bs cx) /\
     rtree tfibsegs B ly3 S3 W3 mem (F + 0x20) (PjTree.JObj []) [] /\
     (exists num, PjStruct.pj_hdr tfibsegs (mrestrict (w_H W3) mem) (F + 0x20) 6 num 0 0 0 0 0) /\
     pobj tfibsegs B ly3 S3 W3 mem (F + 0x20) /\ pobj tfibsegs B ly3 S3 W3 mem (F + 0x80) /\
     pobj tfibsegs B ly3 S3 W3 mem (F + 0xe0) /\ pobj tfibsegs B ly3 S3 W3 mem (F + 0x140) /\
     val_mem tfibsegs (mrestrict (w_H W3) mem) (F + 0x1a0) 8 0 /\
     range_addressable (aview tfibsegs (w_H W3) mem) SHADOW_OFF (F + 0x1a0) 8 /\
     fs_glob tfibsegs W3 mem live peak cnt SIZE_MAXZ /\
     live = c_live cx + FSH_Fn_writer.enc_size len + FSH_Fn_writer.dec_size tb2 /\
     blocks_bytes S3 <= blocks_bytes (c_S cx) + LIVE_8212c cx /\
     c_cnt cx <= cnt <= c_cnt cx + CNT_8212c cx /\ k <= K_8212c cx).
End inv13.

(* ================= the bcmp-return boundary (B1: segment 11 -> segment 12) =================
   Segment 11 (0x82078..0x82098: `beqz a0` on decode's answer, `mv s9, a0`, `ld a0, 0(s11)` of n, `bne a0, s4`,
   `beqz s4`, bcmp (s9 = dec, s5 = bd, s4 = |bs|)) has TWO exits, so the meeting point is two boundaries:
   - |bs| > 0: bcmp returns to 0x8209c; the state is crt_ss_ret 0x8209c crt_cs1 crt_csF and the invariant is
     crtB_INV_8209c, which adds bcmp's answer a0 = 0 (dec = bd) for the `bnez a0` there;
   - |bs| = 0: `beqz s4` at 0x82088 jumps over the bcmp to 0x820a0; the state is crt_ss_ret 0x820a0 crt_cs1 crt_csF and
     the invariant is crtB_INV_820a0 (a0 is dead from 0x820a0: the next read of a0 is `mv a0, s10` at 0x8211c).
   Since 0x82068 (crt_INV_82068): decode (0x82074) made `dec`, a live reader block of dec_size tb2 bytes holding bs,
   whose head joins U, and nothing else allocated or freed; s9 = dec. The want block's size is written enc_size len,
   the same number as crt_INV_82068's (len + 2) / 3 * 4 + 1, and same's size is the existential nsame (|tb| + 1 at
   0x82068), which is crt_INV_8212c's form. The budgets are 0x8212c's: the two pj_object calls between here and 0x8212c
   tick 0 and allocate nothing, and the runtime bcmp adds nothing either. s11 (F + 0x1c0 here) is not stated: segment 12
   reloads it from slot 0x20 at 0x82114. *)
Section inv12. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Definition crtB_INV_820a0 : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  let mem := ms_mem ms3 in let F := crt_F cx in let len := Z.of_nat (length (c_bs cx)) in
  let tb2 := WriterSpec.b64_enc (c_bs cx) in
  ew E 18 = Z_to_bv 64 (c_text cx) /\ ew E 20 = Z_to_bv 64 len /\
  ew E 21 = Z_to_bv 64 (c_bd cx) /\ ew E 22 = Z_to_bv 64 (F + 0xe0) /\ ew E 23 = Z_to_bv 64 (F + 0x80) /\
  ew E 26 = Z_to_bv 64 (F + 0x20) /\
  (exists same nsame dec live peak cnt,
     ew E 24 = Z_to_bv 64 same /\ ew E 25 = Z_to_bv 64 dec /\
     Permutation (ablocks B ly3 S3)
       (ablocks B (c_ly cx) (c_S cx) ++
        [(c_text cx - HEAD, FSH_Fn_writer.enc_size len + HEAD); (c_want cx, FSH_Fn_writer.enc_size len);
         (same, nsame); (dec - HEAD, FSH_Fn_writer.dec_size tb2 + HEAD)]) /\
     Permutation U3 (c_U cx ++ [(c_text cx - HEAD, HEAD); (dec - HEAD, HEAD)]) /\
     FSupoisonU.fs_heads B ly3 S3 U3 /\
     fs_rblock tfibsegs B ly3 S3 W3 mem (c_text cx) (FSH_Fn_writer.enc_size len) /\
     zbytes_at tfibsegs W3 mem (c_text cx) (tb2 ++ [0]) /\ cstr_ok tfibsegs W3 mem (c_text cx) tb2 /\
     fs_rblock tfibsegs B ly3 S3 W3 mem dec (FSH_Fn_writer.dec_size tb2) /\
     zbytes_at tfibsegs W3 mem dec (c_bs cx) /\
     fs_glob tfibsegs W3 mem live peak cnt SIZE_MAXZ /\
     live = c_live cx + FSH_Fn_writer.enc_size len + FSH_Fn_writer.dec_size tb2 /\
     blocks_bytes S3 <= blocks_bytes (c_S cx) + LIVE_8212c cx /\
     c_cnt cx <= cnt <= c_cnt cx + CNT_8212c cx /\ k <= K_8212c cx).
Definition crtB_INV_8209c : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 => ew E 10 = Z_to_bv 64 0 /\ crtB_INV_820a0 cx E k ly3 S3 U3 W3 ms3 md3.
End inv12.
Definition crtB_ss_8209c : sstate := crt_ss_ret 0x8209c crt_cs1 crt_csF.
Definition crtB_ss_820a0 : sstate := crt_ss_ret 0x820a0 crt_cs1 crt_csF.

(* the text and the decoded block fit their blocks (WriterSpecFacts.b64_enc_length) *)
Lemma crtB_len_text : forall bs : list Z,
  Z.of_nat (length (WriterSpec.b64_enc bs ++ [0])) = FSH_Fn_writer.enc_size (Z.of_nat (length bs)).
Proof.
intros bs. rewrite length_app, Nat2Z.inj_add, WriterSpecFacts.b64_enc_length, Nat2Z.inj_mul, Nat2Z.inj_div,
  Nat2Z.inj_add. unfold FSH_Fn_writer.enc_size. cbn [length Z.of_nat]. lia.
Qed.
Lemma crtB_len_dec : forall bs : list Z,
  Z.of_nat (length bs) <= FSH_Fn_writer.dec_size (WriterSpec.b64_enc bs).
Proof.
intros bs. unfold FSH_Fn_writer.dec_size.
rewrite WriterSpecFacts.b64_enc_length, Nat2Z.inj_mul, Nat2Z.inj_div, Nat2Z.inj_add.
cbn [Z.of_nat]. Z.div_mod_to_equations. lia.
Qed.

(* the div / mod arithmetic of the frame objects, stated with no context (lia after Z.div_mod_to_equations in a
   large proof context blows up) *)
Lemma crtB_m8 : forall F, F mod 32 = 0 -> F mod 8 = 0.
Proof. intros F H. Z.div_mod_to_equations. lia. Qed.
Lemma crtB_m8_add : forall F o, F mod 32 = 0 -> o mod 8 = 0 -> (F + o) mod 8 = 0.
Proof. intros F o H1 H2. Z.div_mod_to_equations. lia. Qed.
(* no shadow byte of a frame byte lies in the frame (the frame is application memory, low or high) *)
Lemma crtB_sh_out : forall {rc : YM05.RunCeil} F x lo hi, 4096 <= F ->
  (F + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= F /\ F + 512 <= alloc_ceiling) ->
  F <= x < F + 512 -> F <= lo -> hi <= F + 512 -> ~ (lo <= shadow_addr x < hi).
Proof.
intros rc0 F x lo hi H0 Hm Hx Hlo Hhi. pose proof (@alloc_ceiling_lt rc0) as HC47.
change (2 ^ 47) with 140737488355328 in HC47. unfold shadow_addr, SHADOW_OFF. Z.div_mod_to_equations. lia.
Qed.

(* the stack room of the call, read off STK_check_round_trip's definition (no computation of it: it unfolds through
   every callee's STK) *)
Lemma crtB_zmaxl_ge : forall x l, In x l -> x <= zmaxl l.
Proof.
intros x l. induction l as [|y t IH]; [intros []|].
intros [<-|H]; cbn [zmaxl fold_right]; [lia | specialize (IH H); unfold zmaxl in IH; lia].
Qed.
Lemma crtB_stk13 : STK_pj_object + 208 <= STK_check_round_trip /\ 0 <= STK_pj_object /\ STK_pj_object <= 8192.
Proof.
assert (H0 : STK_pj_object = ltac:(let v := eval vm_compute in STK_pj_object in exact v))
  by (unfold STK_pj_object, zmaxl, STK_RT_INTRIN, ESTACK, FRAME_pj_object; reflexivity).
unfold STK_check_round_trip.
match goal with |- context [zmaxl ?l] =>
  assert (Hm : STK_pj_object <= zmaxl l) by (apply crtB_zmaxl_ge; repeat (first [left; reflexivity | right]))
end.
unfold FRAME_check_round_trip. lia.
Qed.

Section seg13. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis PJ_OBJECT : @pj_object_spec fx rc SK tfibsegs B.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* the call of pj_object (state): its premises from crtB_INV_82124, and crt_INV_8212c from its post *)
Lemma crtB_hcall13 :
  crt_hcall SK B crtB_sc13 A_pj_object 0x8212c STK_pj_object (crtB_INV_82124 B) (crt_INV_8212c B).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 regsC memC mdC HB HE HINV HJC HARUC Hfr HSB RG HPRE HFRL HTOP.
destruct crtB_site13 as (_ & H10 & HSV).
destruct HINV as (E18 & E20 & E21 & E22 & E23 & E26 & E27 & same & nsame & dec & live & peak & cnt & E24 & E25 &
  HPB & HPU & HHD & HRT & HZT & HCT & HRD & HZD & HTD & HHDd & HPd & HPs & HPv & HPb & HVN & HRN & HGL & HLV &
  HBB & HCN & HK).
set (F := crt_F cx) in *.
pose proof HE as (E2 & _).
pose proof HJC as (HAR3 & Hly3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct crtB_stk13 as (STKo & STK0 & STK1).
assert (Hsp0 : alloc_ceiling + STK_check_round_trip <= spZ (c_regs cx)) by lia.
assert (EF : frame_addr ly3 3 (c_pos cx) = F) by exact (crt_F_ly cx _ ly3 Hly3).
assert (Hin : In (3, c_pos cx) (frames S3)) by (rewrite Hfr; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ 3 (c_pos cx) HAR3 Hin) as (HF4096 & HFceil & _).
rewrite EF in HF4096. rewrite EF, crt_frame3 in HFceil.
destruct (crt_sp1_facts cx Hal16 ltac:(lia)) as (Hsp1 & _ & _).
assert (G2 : sr_get (ss_regs crtB_sc13) 2%bv = SOff 2 0) by (vm_compute; reflexivity).
assert (Esp : spZ regsC = crt_sp1 cx) by (unfold spZ; rewrite RG, G2, fsw_SOff0; exact E2).
assert (R10 : YK11.getr regsC 10%bv = w64 (F + 0x80)) by (rewrite RG, H10, fsw_SOff0, E23; reflexivity).
pose proof (PJ_OBJECT ly3 S3 U3 W3 regsC memC mdC (crt_ch1 cx) (F + 0x80) live peak cnt SIZE_MAXZ HPRE HHD R10
  (pobj_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC (F + 0x80) HAR3 HSB HPs)
  ltac:(left; rewrite Esp; lia)
  (fs_glob_below W3 (ms_mem ms3) memC live peak cnt SIZE_MAXZ HSB HGL)) as HC.
exists [(F + 0x80, F + 0x80 + 56)], 0. eexists. split; [exact HC|].
split.
{ intros a (rr & [<-|[]] & Ha). cbn [fst snd] in Ha. right; right; right; left. unfold in_frames. exists 3, (c_pos cx).
  split; [left; reflexivity|]. left. unfold in_zr, frame_rng; cbn [fst snd]. rewrite EF, crt_frame3. lia. }
split.
{ intros a Ha (rr & [<-|[]] & Hr). cbn [fst snd] in Hr. rewrite crt_frame3 in Ha. lia. }
intros W' c' HP.
destruct HP as (ly' & S' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HPr & HQ).
exists ly', S', U3, regs', mem', md'.
split; [exact Ec|]. split; [exact HJc|]. split; [exact OK'|]. split; [exact PO'|]. split; [exact HPr|].
intros HJ' HARU'.
destruct HQ as (Eab & HRTs & HPs2 & HGL2).
pose proof HJc as (HARc & Hlyc & _ & _ & _ & Hfrc & _).
set (FPc := [(F + 0x80, F + 0x80 + 56)]).
assert (NF : forall a, (a < F + 0x80 \/ F + 0x80 + 56 <= a) -> ~ inFP FPc a)
  by (intros a Ha (rr & [<-|[]] & Hr); cbn [fst snd] in Hr; lia).
(* a heap block's byte and a frame byte other than state's, read the same after the call *)
assert (KB : forall p n i, In (p, n) (ablocks B ly3 S3) -> 0 <= i < req_size n ->
  aview tfibsegs (w_H W') mem' (p + i) = aview tfibsegs (w_H W3) memC (p + i)).
{ intros p n i Hp Hi. apply (crt_keep_blk SK B ly3 S3 U3 W3 memC mdC ly' S' U3 W' mem' md' STK_pj_object (spZ regsC)
    FPc 0 p n i HARUC HARU' HJc Hp ltac:(rewrite Eab; exact Hp) Hi).
  apply NF. pose proof (sep_block_frame tfibsegs B LAWS _ _ _ _ _ p n 3 (c_pos cx) HAR3 Hp Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EF, crt_frame3 in Hd. lia. }
assert (KF : forall a, F <= a < F + 512 -> (a < F + 0x80 \/ F + 0x80 + 56 <= a) ->
  aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W3) memC a).
{ intros a Ha Hn. apply (crt_keep_frm SK B ly3 S3 U3 W3 memC mdC ly' S' U3 W' mem' md' STK_pj_object (spZ regsC)
    FPc 0 3 (c_pos cx) a HARUC HARU' HJc Hin); [unfold in_zr, frame_rng; cbn [fst snd]; rewrite EF, crt_frame3; lia|].
  exact (NF a Hn). }
assert (KM : forall x : word, F + 0x20 <= bv_unsigned x < F + 0x20 + 56 ->
  mrestrict (w_H W') mem' x = mrestrict (w_H W3) memC x).
{ intros x Hx. rewrite <- (Z_to_bv_bv_unsigned _ x).
  apply (crtB_mres_keep_frm SK B ly3 S3 U3 W3 memC mdC ly' S' U3 W' mem' md' STK_pj_object (spZ regsC) FPc 0 3 (c_pos cx)
    (bv_unsigned x) HARUC HARU' HJc Hin); [rewrite EF, crt_frame3; lia | apply NF; lia]. }
(* the boundary registers after the call: pj_object keeps s2 .. s11 *)
assert (KR : forall n : nat, (18 <= n <= 27)%nat ->
  sr_get (ss_regs crtB_sc13) (Z_to_bv 5 (Z.of_nat n)) = SOff n 0 -> ew (Ereg regs' (crt_extra cx)) n = ew E n).
{ intros n Hn Hs.
  assert (Hu : Z.of_nat n = bv_unsigned (Z_to_bv 5 (Z.of_nat n))).
  { rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity | change (bv_modulus 5) with 32; lia]. }
  rewrite (ew_Ereg_nat regs' (crt_extra cx) n (Z_to_bv 5 (Z.of_nat n)) Hu).
  rewrite (HPr (Z.of_nat n) ltac:(unfold acallee_saved; lia)), RG, Hs. apply fsw_SOff0. }
unfold crt_INV_8212c. lazy zeta beta. cbn [ms_mem mkst]. fold F.
rewrite (KR 18%nat ltac:(lia) (HSV 18%nat ltac:(lia))),
  (KR 20%nat ltac:(lia) (HSV 20%nat ltac:(lia))),
  (KR 21%nat ltac:(lia) (HSV 21%nat ltac:(lia))),
  (KR 22%nat ltac:(lia) (HSV 22%nat ltac:(lia))),
  (KR 23%nat ltac:(lia) (HSV 23%nat ltac:(lia))),
  (KR 26%nat ltac:(lia) (HSV 26%nat ltac:(lia))),
  (KR 27%nat ltac:(lia) (HSV 27%nat ltac:(lia))).
split; [exact E18|]. split; [exact E20|]. split; [exact E21|]. split; [exact E22|]. split; [exact E23|].
split; [exact E26|]. split; [exact E27|].
exists same, nsame, dec, live, peak, cnt.
rewrite (KR 24%nat ltac:(lia) (HSV 24%nat ltac:(lia))),
  (KR 25%nat ltac:(lia) (HSV 25%nat ltac:(lia))).
split; [exact E24|]. split; [exact E25|].
split; [rewrite Eab; exact HPB|]. split; [exact HPU|].
split; [intros r Hr; rewrite Eab; exact (HHD r Hr)|].
(* every data fact of crtB_INV_82124 first moves from the boundary memory to the call-site memory (the run below
   alloc_ceiling stores nothing: same_below), then across pj_object's journal *)
assert (HRTc := fs_rblock_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC _ _ HAR3 HSB HRT).
assert (HRDc := fs_rblock_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC _ _ HAR3 HSB HRD).
assert (BLW : forall a, 0 <= a < alloc_ceiling ->
  aview tfibsegs (w_H W3) memC a = aview tfibsegs (w_H W3) (ms_mem ms3) a)
  by (intros a Ha; exact (aview_below (w_H W3) (ms_mem ms3) memC alloc_ceiling a HSB Ha)).
assert (BLK : forall p n, fs_rblock tfibsegs B ly3 S3 W3 memC p n -> 4096 + HEAD <= p /\ p + n <= alloc_ceiling)
  by (intros p n Hb; exact (fsw_rblock_low B ly3 S3 W3 _ mdC memC p n HAR3 Hb)).
assert (ZBC : forall p n l, fs_rblock tfibsegs B ly3 S3 W3 memC p n -> Z.of_nat (length l) <= n ->
  zbytes_at tfibsegs W3 (ms_mem ms3) p l -> zbytes_at tfibsegs W3 memC p l).
{ intros p n l Hb Hl Hz. destruct (BLK p n Hb) as (B1 & B2).
  apply (crtB_garr8_keep (w_H W3) (w_H W3) (ms_mem ms3) memC p l); [|exact Hz].
  intros i Hi. apply BLW. unfold HEAD in B1. lia. }
assert (RBK : forall p n, fs_rblock tfibsegs B ly3 S3 W3 memC p n -> fs_rblock tfibsegs B ly' S' W' mem' p n).
{ intros p n (Hp & Hal & Hn & Hv). split; [rewrite Eab; exact Hp|]. split; [exact Hal|]. split; [exact Hn|].
  apply (crtB_val_mem_keep (w_H W3) (w_H W') memC mem' _ 8 _); [|exact Hv].
  intros i Hi. apply (KB _ _ i Hp). pose proof (req_size_pos (n + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hrq).
  unfold HEAD in *. cbn in Hi. lia. }
assert (ZBK : forall p n l, fs_rblock tfibsegs B ly3 S3 W3 memC p n -> Z.of_nat (length l) <= n ->
  zbytes_at tfibsegs W3 memC p l -> zbytes_at tfibsegs W' mem' p l).
{ intros p n l (Hp & _ & Hn & _) Hl Hz. apply (crtB_garr8_keep (w_H W3) (w_H W') memC mem' p l); [|exact Hz].
  intros i Hi. pose proof (req_size_pos (n + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hrq).
  replace (p + i) with ((p - HEAD) + (HEAD + i)) by lia. apply (KB _ _ _ Hp). unfold HEAD in *. lia. }
assert (Ltxt := crtB_len_text (c_bs cx)). assert (Ldec := crtB_len_dec (c_bs cx)).
split; [exact (RBK _ _ HRTc)|].
split.
{ assert (Hl : Z.of_nat (length (WriterSpec.b64_enc (c_bs cx) ++ [0])) <=
    FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx)))) by lia.
  exact (ZBK _ _ _ HRTc Hl (ZBC _ _ _ HRTc Hl HZT)). }
split.
{ pose proof HRTc as (Hpt & _). pose proof (req_size_pos (FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + HEAD)
    ltac:(unfold HEAD; lia)) as (_ & Hrq).
  apply (cstr_ok_kept_blkU B STK_pj_object (spZ regsC) FPc ly3 S3 U3 W3 memC mdC [] ly' S' U3 W' mem' md' 0
    (c_text cx) (WriterSpec.b64_enc (c_bs cx)) _ _ HARUC HJc OK' PO' Hpt ltac:(rewrite Eab; exact Hpt)).
  - unfold HEAD. lia.
  - rewrite length_app in Ltxt. cbn [length] in Ltxt. rewrite Nat2Z.inj_add in Ltxt. cbn [Z.of_nat] in Ltxt. lia.
  - intros a Ha. apply NF. pose proof (sep_block_frame tfibsegs B LAWS _ _ _ _ _ _ _ 3 (c_pos cx) HAR3 Hpt Hin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EF, crt_frame3 in Hd.
    rewrite length_app in Ltxt. cbn [length] in Ltxt. rewrite Nat2Z.inj_add in Ltxt. cbn [Z.of_nat] in Ltxt.
    unfold HEAD in *. lia.
  - intros r Hr. left. exact Hr.
  - exact (cstr_ok_below W3 (ms_mem ms3) memC _ _ HSB HCT). }
split; [exact (RBK _ _ HRDc)|].
split; [exact (ZBK _ _ _ HRDc Ldec (ZBC _ _ _ HRDc Ldec HZD))|].
(* the two objects: doc kept byte for byte, state from the post *)
assert (HTDc := rnode_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC [] (F + 0x20) (PjTree.JObj []) [] HAR3 HSB
  ltac:(lia) ltac:(lia) HTD).
assert (KMb : forall x : word, F + 0x20 <= bv_unsigned x < F + 0x20 + 56 ->
  mrestrict (w_H W3) memC x = mrestrict (w_H W3) (ms_mem ms3) x)
  by (intros x Hx; apply (fsw_mrestrict_below (w_H W3) (ms_mem ms3) memC x HSB); lia).
split; [exact (crtB_obj0_keep B ly3 S3 W3 memC ly' S' W' mem' (F + 0x20) KM HTDc)|].
split; [exact HRTs|].
split.
{ destruct HHDd as (num & Hh). exists num.
  exact (crtB_hdr_keep W3 W' memC mem' _ num KM (crtB_hdr_keep W3 W3 (ms_mem ms3) memC _ num KMb Hh)). }
split; [exact (crtB_obj0_hdr B ly' S' W' mem' (F + 0x80) HRTs)|].
(* the four objects' placements *)
assert (POK : forall o, 0 <= o -> o + 56 <= 512 -> o mod 8 = 0 -> (o + 56 <= 0x80 \/ 0x80 + 56 <= o) ->
  pobj tfibsegs B ly3 S3 W3 (ms_mem ms3) (F + o) -> pobj tfibsegs B ly' S' W' mem' (F + o)).
{ intros o Ho0 Ho1 Ho8 Hoo HP0.
  pose proof (pobj_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC (F + o) HAR3 HSB HP0) as (Harm & _).
  assert (HRA : range_addressable (aview tfibsegs (w_H W3) memC) SHADOW_OFF (F + o) 56)
    by (destruct Harm as [(_ & _ & Hra) | (_ & _ & Hra)]; exact Hra).
  destruct (al_frames _ _ LAWS _ _ _ _ _ 3 (c_pos cx) HAR3 Hin) as (Hm32 & Happ & _).
  rewrite EF in Hm32, Happ. rewrite crt_frame3 in Happ.
  assert (Hin' : In (3, c_pos cx) (frames S')) by (rewrite Hfrc; exact Hin).
  assert (EF' : frame_addr ly' 3 (c_pos cx) = F).
  { rewrite <- EF. unfold frame_addr. destruct Hlyc as (_ & _ & _ & _ & _ & EFl & _). rewrite EFl. reflexivity. }
  split.
  - left. split; [|split].
    + exists 3, (c_pos cx). split; [exact Hin'|]. rewrite EF', crt_frame3.
      split; [lia|]. split; [exact (crtB_m8 F Hm32)|]. lia.
    + exact (crtB_m8_add F o Hm32 Ho8).
    + apply (crtB_RA_keep_frm SK B ly3 S3 U3 W3 memC mdC ly' S' U3 W' mem' md' STK_pj_object (spZ regsC) FPc 0 3
        (c_pos cx) (F + o) 56 HARUC HARU' HJc Hin); [rewrite EF; exact (crtB_m8 F Hm32) | reflexivity
        | rewrite EF; lia | rewrite EF, crt_frame3; lia | | exact HRA].
      intros x Hx (rr & [<-|[]] & Hr). cbn [fst snd] in Hr. cbv [in_app kLowShadowBeg kHighMemBeg] in Happ.
      apply (crtB_sh_out F x (F + 0x80) (F + 0x80 + 56)); [lia | | lia | lia | lia | exact Hr].
      destruct Happ as (_ & [Ha | (Ha1 & Ha2)]); [left; exact Ha | right; split; [exact Ha1 | exact HFceil]].
  - intros i Hi. apply (apresent_writable tfibsegs).
    destruct (al_frames _ _ LAWS _ _ _ _ _ 3 (c_pos cx) (ARU_AR tfibsegs B _ _ _ _ _ _ HARU') Hin')
      as (_ & _ & Hfp' & _).
    rewrite EF', crt_frame3 in Hfp'. destruct (Hfp' (F + o + i) ltac:(lia)) as ((Hh & b & Hb) & _).
    split; [exact Hh|]. exists b.
    rewrite <- (unpoison_app B ly' S' U3 W' mem' md' (F + o + i) HARU').
    + exact Hb.
    + pose proof (@alloc_ceiling_lt rc) as HC47. change (2 ^ 47) with 140737488355328 in HC47.
      change (2 ^ 64) with 18446744073709551616. lia.
    + cbv [in_app kLowShadowBeg kHighMemBeg] in Happ. cbv [SHADOW_OFF kHighMemBeg]. lia. }
split; [exact (POK 0x20 ltac:(lia) ltac:(lia) eq_refl ltac:(lia) HPd)|].
split; [exact HPs2|].
split; [exact (POK 0xe0 ltac:(lia) ltac:(lia) eq_refl ltac:(lia) HPv)|].
split; [exact (POK 0x140 ltac:(lia) ltac:(lia) eq_refl ltac:(lia) HPb)|].
(* the n cell and its shadow *)
split.
{ apply (crtB_val_mem_keep (w_H W3) (w_H W') memC mem' _ 8 _).
  - intros i Hi. cbn in Hi. apply KF; lia.
  - exact (val_mem_below (w_H W3) (ms_mem ms3) memC alloc_ceiling (F + 0x1a0) 8 0 HSB ltac:(lia) ltac:(cbn; lia) HVN). }
split.
{ destruct (al_frames _ _ LAWS _ _ _ _ _ 3 (c_pos cx) HAR3 Hin) as (Hm32 & Happ & _).
  rewrite EF in Hm32, Happ. rewrite crt_frame3 in Happ.
  apply (crtB_RA_keep_frm SK B ly3 S3 U3 W3 memC mdC ly' S' U3 W' mem' md' STK_pj_object (spZ regsC) FPc 0 3
    (c_pos cx) (F + 0x1a0) 8 HARUC HARU' HJc Hin); [rewrite EF; exact (crtB_m8 F Hm32) | reflexivity
    | rewrite EF; lia | rewrite EF, crt_frame3; lia | |].
  - intros x Hx (rr & [<-|[]] & Hr). cbn [fst snd] in Hr. cbv [in_app kLowShadowBeg kHighMemBeg] in Happ.
    apply (crtB_sh_out F x (F + 0x80) (F + 0x80 + 56)); [lia | | lia | lia | lia | exact Hr].
    destruct Happ as (_ & [Ha | (Ha1 & Ha2)]); [left; exact Ha | right; split; [exact Ha1 | exact HFceil]].
  - exact (fsw_range_addressable_below (w_H W3) (ms_mem ms3) memC (F + 0x1a0) 8 HSB ltac:(lia) ltac:(lia) HRN). }
split; [exact HGL2|]. split; [exact HLV|].
split; [rewrite (blocks_bytes_bsum B ly' S'), Eab, <- (blocks_bytes_bsum B ly3 S3); exact HBB|].
split; [exact HCN | lia].
Qed.

(* SEGMENT 13 (0x82124 -> pj_object (state) -> 0x8212c), the generic call crossing at this call *)
Lemma crtB_seg13 :
  crt_from SK B (crt_ss_ret 0x8212c crt_cs1 crt_csF) (crt_INV_8212c B) ->
  crt_from SK B (crt_ss_ret 0x82124 crt_cs1 crt_csF) (crtB_INV_82124 B).
Proof.
intros NEXT. destruct crtB_site13 as (HCS & _ & _).
exact (crt_seg_call SK B 0x82124 A_pj_object 0x8212c crtB_sc13 _ _ STK_pj_object crtB_run13 HCS
  ltac:(change (2 ^ 64) with 18446744073709551616; lia) eq_refl (proj1 (proj2 crtB_stk13))
  (proj1 crtB_stk13) crtB_hcall13 NEXT).
Qed.
End seg13.

(* ================= a segment that starts with `bnez a0` (not taken, a0 = 0) and then runs WITH stores into crt's
   frame / shadow, to a PROGRAM call =================
   FSH_crt_site.crt_seg_call_full with two generalizations and no other change; written with no segment-B name, so it
   can be moved verbatim into lib/A/FSH_crt_site.v: (1) the run starts with the boundary's `bnez a0`, decided by INV's
   a0 = 0 (crt_seg_call_br's two-run shape, here over the FULL four-region boundary state with write window
   FSH_crt_base.crt_awr_ok); (2) the frame region at the call may hold more chunks than crt_csF (csF', e.g. a frame cell
   the run zeroed), and the callee's part also gets the call-site st_ok, so that it can read the run's stores (the
   shadow the run unpoisoned, the cell it wrote). Segment 12 (0x8209c) is its first user. *)
Section brw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

Definition crtB_csite_w (ssC : sstate) (A_c r : Z) (csF' : list YP09.chunk) : Prop :=
  ss_pc ssC = A_c /\ ss_resv ssC = None /\
  nth_error (ss_mem ssC) 0 = Some crt_s0_region /\
  nth_error (ss_mem ssC) 1 = Some (crt_slot_region crt_cs1) /\
  nth_error (ss_mem ssC) 2 = Some (crt_frame_region csF') /\
  In (YP09.mkChunk (fs_frame_bytes 3 - 8) (CVal 8 (SOff 46 0))) csF' /\
  sr_get (ss_regs ssC) 1%bv = SLit r /\ sr_get (ss_regs ssC) 2%bv = SOff 2 0 /\
  sr_get (ss_regs ssC) 3%bv = SOff 3 0 /\ sr_get (ss_regs ssC) 4%bv = SOff 4 0 /\
  sr_get (ss_regs ssC) 8%bv = SOff 8 0 /\ sr_get (ss_regs ssC) 9%bv = SOff 9 0 /\
  sr_get (ss_regs ssC) 19%bv = SOff 19 0.

(* the segment's own part: crt_hcall_full's, plus the call-site st_ok *)
Definition crtB_hcall_w (ss0 ssC : sstate) (A_c r STKc : Z) (INV INV' : crt_inv) : Prop :=
  forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3 regsC memC mdC,
  crt_base B cx -> crt_E cx E -> INV cx E k ly3 S3 U3 W3 ms3 md3 ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 memC) mdC k ->
  ARU tfibsegs B ly3 S3 U3 W3 memC mdC ->
  frames S3 = (3, c_pos cx) :: frames (c_S cx) ->
  frame_of E (ss_mem ss0) (ms_mem ms3) memC ->
  frame_of E (ss_mem ss0) (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) memC) ->
  st_ok tfibsegs E ssC (restrict (w_H W3) (mkst regsC (Z_to_bv 64 A_c) memC (seg_rom tfibsegs))) ->
  (forall rr : bv 5, YK11.getr regsC rr = sv_denot E (sr_get (ss_regs ssC) rr)) ->
  fpreU tfibsegs B STKc ly3 S3 U3 W3 regsC memC mdC (crt_ch1 cx) ->
  Z.of_nat (length (frames S3)) <= FRL_CRT_CALLEE ->
  spZ regsC + 32 <= ly_top ly3 ->
  exists FPc kc (P : world tfibsegs -> config -> Prop),
    SRr tfibsegs W3 (cfg_at tfibsegs A_c regsC memC mdC) P /\
    fsw_fp_sub B (c_ly cx) (c_S cx) ly3 S3 [(3, c_pos cx)] FS_PSTAT_FP FPc /\
    (forall a, crt_F cx + fs_frame_bytes 3 - 8 <= a < crt_F cx + fs_frame_bytes 3 -> ~ inFP FPc a) /\
    (forall W' c', P W' c' -> exists ly' S' U' regs' mem' md',
       c' = mkCfg (mkst regs' (YK11.getr regsC 1%bv) mem' (seg_rom tfibsegs)) md' /\
       ajournal tfibsegs B STKc (spZ regsC) FPc ly3 S3 W3 (unpoison U3 memC) mdC [] ly' S' W'
         (unpoison U' mem') md' kc /\
       upoison_ok B ly' S' U' /\ upoisoned tfibsegs W' mem' U' /\ aregs_preserved regsC regs' /\
       (ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
          (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly' S' W' (unpoison U' mem') md' (k + kc) ->
        ARU tfibsegs B ly' S' U' W' mem' md' ->
        INV' cx (Ereg regs' (crt_extra cx)) (k + kc) ly' S' U' W' (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))
          md')).

(* the call half of crt_seg_call_full, from the call-site machine state ms: the flag word off the frame region,
   crt_site_pre, the segment's own part, crt_after_call, then the walk from r *)
Lemma crtB_call_w_core : forall r0 A_c r ssC csF' (INV INV' : crt_inv) STKc cx E k ly3 S3 U3 (W3 : world tfibsegs)
  ms3 md3 ms mdC,
  crtB_csite_w ssC A_c r csF' -> 4096 <= r < 2 ^ 64 -> r mod 2 = 0 ->
  0 <= STKc -> STKc + 208 <= STK_check_round_trip ->
  crtB_hcall_w (crt_ss_ret r0 crt_cs1 crt_csF) ssC A_c r STKc INV INV' ->
  crt_from SK B (crt_ss_ret r crt_cs1 crt_csF) INV' ->
  crt_base B cx -> crt_E cx E -> crt_frame_ok cx S3 W3 ms3 -> INV cx E k ly3 S3 U3 W3 ms3 md3 ->
  st_ok tfibsegs E ssC (restrict (w_H W3) ms) ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms)) mdC k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms) mdC ->
  frame_of E (ss_mem (crt_ss_ret r0 crt_cs1 crt_csF)) (ms_mem ms3) (ms_mem ms) ->
  frame_of E (ss_mem (crt_ss_ret r0 crt_cs1 crt_csF)) (mrestrict (w_H W3) (ms_mem ms3))
    (mrestrict (w_H W3) (ms_mem ms)) ->
  SRr tfibsegs W3 (mkCfg ms mdC) (crt_post SK B cx).
Proof.
intros r0 A_c r ssC csF' INV INV' STKc cx E k ly3 S3 U3 W3 ms3 md3 ms mdC HCS Hr Hr2 HSTKc HSTK HCALL NEXT
  HB HE HFO HINV HSC HJC HARUC HFt HFrt.
destruct HCS as (Hpc & Hres & M0 & M1 & M2 & Hfl & G1 & G2 & G3 & G4 & G8 & G9 & G19).
pose proof HFO as (Hfr & Hnin & _).
pose proof HE as (E2 & E3 & E4 & E8 & E9 & E19 & EX).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HB as (HPRE & _). pose proof (fsw_sp B _ _ _ _ _ _ _ _ _ (proj1 HPRE)) as (Hal16 & Hceil0 & H47 & HS0).
pose proof (@alloc_ceiling_value rc) as (HCr & _).
pose proof (fsw_realign_facts (spZ (c_regs cx) - 192) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity))
  as (F1 & F2 & F3).
assert (Hsp1 : spZ (c_regs cx) - 208 <= crt_sp1 cx <= spZ (c_regs cx) - 192) by (unfold crt_sp1; lia).
pose proof HJC as (_ & Hly0 & _).
pose proof (crt_F_ly cx _ ly3 Hly0) as EF0.
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARUC) as HAR0.
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfr; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ 3 (c_pos cx) HAR0 Hin3) as (HF4096 & HFceil & _).
rewrite EF0 in HF4096, HFceil. rewrite crt_frame3 in HFceil.
pose proof (crt_mkst (w_H W3) E ssC ms HSC Hres) as Ems. rewrite Hpc in Ems.
set (regsC := ms_regs ms) in *. set (memC := ms_mem ms) in *.
assert (RG : forall rr : bv 5, YK11.getr regsC rr = sv_denot E (sr_get (ss_regs ssC) rr))
  by (intros rr; exact (st_ok_restrict_reg tfibsegs (w_H W3) E ssC ms rr HSC)).
assert (R1 : YK11.getr regsC 1%bv = Z_to_bv 64 r) by (rewrite RG, G1; reflexivity).
assert (R2 : YK11.getr regsC 2%bv = ew E 2) by (rewrite RG, G2; apply fsw_SOff0).
assert (R3 : YK11.getr regsC 3%bv = ew E 3) by (rewrite RG, G3; apply fsw_SOff0).
assert (R4 : YK11.getr regsC 4%bv = ew E 4) by (rewrite RG, G4; apply fsw_SOff0).
assert (R8 : YK11.getr regsC 8%bv = ew E 8) by (rewrite RG, G8; apply fsw_SOff0).
assert (R9 : YK11.getr regsC 9%bv = ew E 9) by (rewrite RG, G9; apply fsw_SOff0).
assert (R19 : YK11.getr regsC 19%bv = ew E 19) by (rewrite RG, G19; apply fsw_SOff0).
assert (HR0 : region_ok tfibsegs E (mrestrict (w_H W3) memC) crt_s0_region)
  by exact (fsw_region_nth E ssC (restrict (w_H W3) ms) 0 crt_s0_region HSC M0).
assert (HRs : region_ok tfibsegs E (mrestrict (w_H W3) memC) (crt_slot_region crt_cs1))
  by exact (fsw_region_nth E ssC (restrict (w_H W3) ms) 1 (crt_slot_region crt_cs1) HSC M1).
assert (HRf : region_ok tfibsegs E (mrestrict (w_H W3) memC) (crt_frame_region csF'))
  by exact (fsw_region_nth E ssC (restrict (w_H W3) ms) 2 (crt_frame_region csF') HSC M2).
(* the flag word, read off the frame REGION at the call state *)
pose proof (al_flag _ _ LAWS _ _ _ _ _ 3 (c_pos cx) (ARU_AR tfibsegs B _ _ _ _ _ _ HARUC)
  ltac:(rewrite Hfr; left; reflexivity)) as (_ & _ & Hflapp & Hflc).
pose proof HJC as (_ & HlyC & _).
rewrite (crt_FL_ly cx _ ly3 HlyC) in Hflapp, Hflc.
assert (HFLr : 0 <= crt_FL cx < 2 ^ 64) by (unfold in_app in Hflapp; lia).
assert (HFv : bv_unsigned (ew E 47) = crt_F cx)
  by (rewrite (crt_E_F cx E HE); apply wz; lia).
assert (Hflval : val_mem tfibsegs (mrestrict (w_H W3) memC) (crt_F cx + (fs_frame_bytes 3 - 8)) 8 (crt_FL cx)).
{ exact (fsw_field E (mrestrict (w_H W3) memC) 47 (crt_F cx) csF' 0 (fs_frame_bytes 3) 0 (fs_frame_bytes 3)
    (fs_frame_bytes 3 - 8) 8 (SOff 46 0) (crt_FL cx) HRf HFv Hfl
    ltac:(rewrite fsw_SOff0; exact (crt_E_FL cx E HE)) ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(cbn; lia)). }
assert (Hflag' : rdword (aview tfibsegs (w_H W3) memC) (crt_F cx + fs_frame_bytes 3 - 8) = Some (crt_FL cx)).
{ replace (crt_F cx + fs_frame_bytes 3 - 8) with (crt_F cx + (fs_frame_bytes 3 - 8)) by lia.
  exact (AF0x.val_mem_rdword (w_H W3) memC _ (crt_FL cx) HFLr Hflval). }
assert (Hrok : YK0s.ret_ok (Z_to_bv 64 r)) by (apply ret_ok_even; rewrite (wz r) by lia; exact Hr2).
destruct (crt_site_pre SK B cx E k ly3 S3 U3 W3 ms mdC ssC r STKc HB HE HJC HARUC (conj Hfr (conj Hnin Hflag'))
  HSC G1 G2 G3 G4 G8 M0 Hr Hrok HSTKc HSTK) as (HPREc & _ & HFRL & HTOPc).
assert (HSC' : st_ok tfibsegs E ssC (restrict (w_H W3) (mkst regsC (Z_to_bv 64 A_c) memC (seg_rom tfibsegs))))
  by (rewrite <- Ems; exact HSC).
rewrite Ems. change (mkCfg (mkst regsC (Z_to_bv 64 A_c) memC (seg_rom tfibsegs)) mdC)
  with (cfg_at tfibsegs A_c regsC memC mdC).
destruct (HCALL cx E k ly3 S3 U3 W3 ms3 md3 regsC memC mdC HB HE HINV HJC HARUC Hfr HFt HFrt HSC' RG HPREc HFRL HTOPc)
  as (FPc & kc & P & HSRr & HFP & HFL & HK).
eapply SRr_bind; [exact HSRr|].
intros W' c' Hle HPc.
destruct (HK W' c' HPc) as (ly' & S' & U' & regs' & mem' & md' & -> & HJc & OK' & PO' & HP & HINV').
rewrite R1.
assert (V : forall n z, bv_unsigned (ew E n) = z -> 0 <= z < 2 ^ 64 -> ew E n = Z_to_bv 64 z)
  by (intros n z Hz Hr64; apply bv_eq; rewrite Hz; symmetry; apply wz; exact Hr64).
assert (Esp : spZ regsC = crt_sp1 cx) by (unfold spZ; rewrite R2; exact E2).
assert (HSV : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) memC) (spZ (c_regs cx))) crt_sv_chunks).
{ destruct HR0 as (_ & _ & _ & Hc). cbn [crt_s0_region fs_ret_s0_region YP09.r_base YP09.r_chunks base_val] in Hc.
  rewrite E8 in Hc. exact Hc. }
assert (HCS1 : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) memC) (crt_sp1 cx)) crt_cs1).
{ destruct HRs as (_ & _ & _ & Hc). cbn [crt_slot_region YP09.r_base YP09.r_chunks base_val] in Hc.
  rewrite E9 in Hc. exact Hc. }
assert (HCSF : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) memC) (crt_F cx)) crt_csF).
{ destruct HRf as (_ & _ & _ & Hc). cbn [crt_frame_region YP09.r_base YP09.r_chunks base_val] in Hc.
  rewrite HFv in Hc. rewrite Forall_forall in Hc |- *. intros c Hcin. apply Hc.
  unfold crt_csF in Hcin. destruct Hcin as [<-|[]]. exact Hfl. }
rewrite Esp in HJc.
assert (Q2 : YK11.getr regsC 2%bv = Z_to_bv 64 (crt_sp1 cx)) by (rewrite R2; apply V; [exact E2 | lia]).
assert (Q3 : YK11.getr regsC 3%bv = YK11.getr (c_regs cx) 3%bv) by (rewrite R3; exact E3).
assert (Q4 : YK11.getr regsC 4%bv = YK11.getr (c_regs cx) 4%bv) by (rewrite R4; exact E4).
assert (Q8 : YK11.getr regsC 8%bv = Z_to_bv 64 (spZ (c_regs cx))) by (rewrite R8; apply V; [exact E8 | lia]).
assert (Q9 : YK11.getr regsC 9%bv = Z_to_bv 64 (crt_sp1 cx)) by (rewrite R9; apply V; [exact E9 | lia]).
pose proof (shadow_addr_bounds (crt_F cx) ltac:(lia)) as (HSF1 & HSF2).
assert (Q19 : YK11.getr regsC 19%bv = Z_to_bv 64 (crt_SF cx))
  by (rewrite R19; apply V; [exact E19 | unfold crt_SF, kLowMemEnd, kHighShadowEnd in *; lia]).
assert (HcsFin : Forall (fun c => 0 <= YP09.c_off c /\ 0 <= YP09.c_len c /\ YP09.c_off c + YP09.c_len c <= fs_frame_bytes 3)
  crt_csF) by (unfold crt_csF; rewrite crt_frame3; apply Forall_cons; [cbn; lia | apply Forall_nil]).
assert (HcsFat : crt_atom_chunks crt_csF)
  by (unfold crt_atom_chunks, crt_csF; apply Forall_cons; [do 4 eexists; split; [reflexivity | lia] | apply Forall_nil]).
assert (HcsFnf : forall c, In c crt_csF -> forall i, 0 <= i < YP09.c_len c -> ~ inFP FPc (crt_F cx + YP09.c_off c + i)).
{ intros c Hc i Hi. unfold crt_csF in Hc. destruct Hc as [<-|[]]. cbn in Hi. apply HFL. cbn. rewrite crt_frame3. lia. }
assert (HflNF : forall i, 0 <= i < 8 -> ~ inFP FPc (crt_F cx + fs_frame_bytes 3 - 8 + i)) by (intros i Hi; apply HFL; lia).
destruct (crt_after_call (SKfp := SK) B cx E k ly3 S3 U3 W3 (mkst regsC (Z_to_bv 64 A_c) memC (seg_rom tfibsegs)) mdC
  STKc FPc ly' S' U' W' regs' mem' md' kc r crt_csF HE HJC HARUC (conj Hfr (conj Hnin Hflag'))
  Q2 Q3 Q4 Q8 Q9 Q19 HSV HCS1 HCSF HcsFin HcsFat HcsFnf HflNF HJc OK' PO' HFP HP HSTKc ltac:(lia))
  as (HJ' & HARU' & HFO' & HE' & HS').
exact (NEXT cx (Ereg regs' (crt_extra cx)) (k + kc) ly' S' U' W' (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))
  md' HB HE' HJ' HARU' HFO' (HINV' HJ' HARU') HS').
Qed.

(* the run's write window from a boundary: its four regions (FSH_crt_base.crt_awr_ok) *)
Lemma crtB_awr4 : forall r0 cx E k ly3 S3 U3 (W3 : world tfibsegs) mem md3,
  crt_base B cx -> crt_E cx E ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 mem) md3 k ->
  ARU tfibsegs B ly3 S3 U3 W3 mem md3 -> frames S3 = (3, c_pos cx) :: frames (c_S cx) ->
  awr_ok tfibsegs B E (ss_mem (crt_ss_ret r0 crt_cs1 crt_csF)) STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP
    (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3 [(3, c_pos cx)] (frames (c_S cx)).
Proof.
intros r0 cx E k ly3 S3 U3 W3 mem md3 HB HE HJ HARU Hfr.
pose proof HB as (HPRE & _). pose proof (fsw_sp B _ _ _ _ _ _ _ _ _ (proj1 HPRE)) as (Hal16 & Hceil0 & H47 & HS0).
pose proof (@alloc_ceiling_value rc) as (HCr & _).
pose proof HJ as (_ & Hly0 & _).
pose proof (crt_F_ly cx _ ly3 Hly0) as EF0.
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARU) as HAR0.
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfr; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ 3 (c_pos cx) HAR0 Hin3) as (HF4096 & HFceil & _).
rewrite EF0 in HF4096, HFceil. rewrite crt_frame3 in HFceil.
exact (crt_awr_ok B cx E ly3 S3 crt_cs1 crt_csF HE ltac:(lia) ltac:(lia) EF0 ltac:(lia)).
Qed.

(* a segment that runs WITH stores into crt's frame / shadow from the boundary at r0 to a program call *)
Lemma crtB_seg_call_w : forall r0 A_c r ssC csF' (INV INV' : crt_inv) STKc,
  sym_run_toN tfibsegs crt_tbl FUEL A_c (crt_ss_ret r0 crt_cs1 crt_csF) = (ssC, RS_running) ->
  crtB_csite_w ssC A_c r csF' -> 4096 <= r < 2 ^ 64 -> r mod 2 = 0 ->
  0 <= STKc -> STKc + 208 <= STK_check_round_trip ->
  crtB_hcall_w (crt_ss_ret r0 crt_cs1 crt_csF) ssC A_c r STKc INV INV' ->
  crt_from SK B (crt_ss_ret r crt_cs1 crt_csF) INV' ->
  crt_from SK B (crt_ss_ret r0 crt_cs1 crt_csF) INV.
Proof.
intros r0 A_c r ssC csF' INV INV' STKc HRUN HCS Hr Hr2 HSTKc HSTK HCALL NEXT.
intros cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU HFO HINV HS.
pose proof HFO as (Hfr & _).
pose proof (crtB_awr4 r0 cx E k ly3 S3 U3 W3 (ms_mem ms3) md3 HB HE HJ HARU Hfr) as AWR.
eapply (fsw_run_to_AJU B crt_tbl crt_tbl_ok W3 FUEL A_c E (crt_ss_ret r0 crt_cs1 crt_csF) ssC RS_running ms3
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS HRUN I HARU HJ AWR).
intros ms mat HSC HJC HARUC HF HFr HG.
exact (crtB_call_w_core r0 A_c r ssC csF' INV INV' STKc cx E k ly3 S3 U3 W3 ms3 md3 ms _ HCS Hr Hr2 HSTKc HSTK
  HCALL NEXT HB HE HFO HINV HSC HJC HARUC HF HFr).
Qed.

(* the same after the boundary's `bnez a0` (not taken: INV's a0 = 0), crt_seg_call_br's two-run shape *)
Lemma crtB_seg_call_brw : forall r0 A_c r sb ssC csF' (INV INV' : crt_inv) STKc,
  sym_runN tfibsegs crt_tbl FUEL (crt_ss_ret r0 crt_cs1 crt_csF) =
    (sb, RS_stopped (SR_branch BC_NE (SOff 10 0) (SLit 0))) ->
  sym_run_toN tfibsegs crt_tbl FUEL A_c (add_cond sb crt_c0) = (ssC, RS_running) ->
  ss_mem sb = ss_mem (crt_ss_ret r0 crt_cs1 crt_csF) ->
  crtB_csite_w ssC A_c r csF' -> 4096 <= r < 2 ^ 64 -> r mod 2 = 0 ->
  0 <= STKc -> STKc + 208 <= STK_check_round_trip ->
  (forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3, INV cx E k ly3 S3 U3 W3 ms3 md3 -> ew E 10 = Z_to_bv 64 0) ->
  crtB_hcall_w (crt_ss_ret r0 crt_cs1 crt_csF) ssC A_c r STKc INV INV' ->
  crt_from SK B (crt_ss_ret r crt_cs1 crt_csF) INV' ->
  crt_from SK B (crt_ss_ret r0 crt_cs1 crt_csF) INV.
Proof.
intros r0 A_c r sb ssC csF' INV INV' STKc HRUN1 HRUN2 Hmem1 HCS Hr Hr2 HSTKc HSTK HZ HCALL NEXT.
intros cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU HFO HINV HS.
pose proof HFO as (Hfr & _).
pose proof (crtB_awr4 r0 cx E k ly3 S3 U3 W3 (ms_mem ms3) md3 HB HE HJ HARU Hfr) as AWR.
(* run 1: to the `bnez a0` *)
eapply (fsw_run_AJU B crt_tbl crt_tbl_ok W3 FUEL E (crt_ss_ret r0 crt_cs1 crt_csF) sb _ ms3
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS HRUN1 I HARU HJ AWR).
intros ms1 mat1 HS1 HJ1 HARU1 HF1 HFr1 HG1.
(* the not-taken arm: a0 = 0 *)
pose proof (st_ok_add_cond_neg tfibsegs E sb _ BC_NE (SOff 10 0) (SLit 0) HS1
  (crt_no_trap_ne E (HZ _ _ _ _ _ _ _ _ _ HINV))) as HS1c.
change (add_cond sb (mkAC (neg_bc BC_NE) (SOff 10 0) (SLit 0))) with (add_cond sb crt_c0) in HS1c.
assert (AWR2 : awr_ok tfibsegs B E (ss_mem (add_cond sb crt_c0)) STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP
    (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3 [(3, c_pos cx)] (frames (c_S cx)))
  by (change (ss_mem (add_cond sb crt_c0)) with (ss_mem sb); rewrite Hmem1; exact AWR).
(* run 2: to the callee *)
eapply (fsw_run_to_AJU B crt_tbl crt_tbl_ok W3 FUEL A_c E (add_cond sb crt_c0) ssC RS_running ms1
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS1c HRUN2 I HARU1 HJ1 AWR2).
intros ms mat HSC HJC HARUC HF HFr HG.
assert (HSK : YP09.skeleton (ss_mem (crt_ss_ret r0 crt_cs1 crt_csF)) = YP09.skeleton (ss_mem (add_cond sb crt_c0)))
  by (change (ss_mem (add_cond sb crt_c0)) with (ss_mem sb); rewrite Hmem1; reflexivity).
exact (crtB_call_w_core r0 A_c r ssC csF' INV INV' STKc cx E k ly3 S3 U3 W3 ms3 md3 ms _ HCS Hr Hr2 HSTKc HSTK
  HCALL NEXT HB HE HFO HINV HSC HJC HARUC (frame_of_trans E _ _ _ _ _ HSK HF1 HF)
  (frame_of_trans E _ _ _ _ _ HSK HFr1 HFr)).
Qed.
End brw.

(* ================= segment 12: 0x8209c (or 0x820a0) -> the 29 shadow stores 0x820a0-0x82110, `ld s11, 0x20(s1)`,
   `sd zero, 0(s11)`, `mv a0, s10` -> pj_object (doc = F + 0x20) -> 0x82124 =================
   Two entries (the two exits of segment 11): crtB_seg12 from crtB_ss_8209c (the `bnez a0` on bcmp's answer first,
   crtB_seg_call_brw) and crtB_seg12z from crtB_ss_820a0 (crtB_seg_call_w). The run writes the frame's shadow (region 3:
   the 7 granules of each of doc / state / v / back and the n cell's granule set to 0) and the frame's n cell (region
   2's chunk at 0x1a0); the callee part (crtB_hcall12) reads them off the call-site st_ok. Port of d25a984c903
   lib/A/Prog/check_round_trip_sd3.v crt_objs_seg (:371) first half, restated over the S0 predicates. MEASURED by the
   engine over crt_tbl. *)
Definition crtB_csF12 : list YP09.chunk :=
  [YP09.mkChunk 416 (CVal 8 (SLit 0)); YP09.mkChunk (fs_frame_bytes 3 - 8) (CVal 8 (SOff 46 0))].
Definition crtB_sb12 : sstate := Eval vm_compute in fst (sym_runN tfibsegs crt_tbl FUEL crtB_ss_8209c).
Lemma crtB_br12 : sym_runN tfibsegs crt_tbl FUEL (crt_ss_ret 0x8209c crt_cs1 crt_csF) =
  (crtB_sb12, RS_stopped (SR_branch BC_NE (SOff 10 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma crtB_mem12 : ss_mem crtB_sb12 = ss_mem (crt_ss_ret 0x8209c crt_cs1 crt_csF).
Proof. vm_compute. reflexivity. Qed.
Definition crtB_sc12 : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL A_pj_object (add_cond crtB_sb12 crt_c0)).
Lemma crtB_run12 : sym_run_toN tfibsegs crt_tbl FUEL A_pj_object (add_cond crtB_sb12 crt_c0) = (crtB_sc12, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition crtB_sc12z : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL A_pj_object crtB_ss_820a0).
Lemma crtB_run12z :
  sym_run_toN tfibsegs crt_tbl FUEL A_pj_object (crt_ss_ret 0x820a0 crt_cs1 crt_csF) = (crtB_sc12z, RS_running).
Proof. vm_compute. reflexivity. Qed.
(* the shadow region at the call: the run's 29 one-byte zero stores *)
Definition crtB_sh12 : list YP09.chunk := Eval vm_compute in
  match nth_error (ss_mem crtB_sc12) 3 with Some rg => YP09.r_chunks rg | None => [] end.
Definition crtB_site12 (ssC : sstate) : Prop :=
  crtB_csite_w ssC A_pj_object 0x82124 crtB_csF12 /\
  nth_error (ss_mem ssC) 3 =
    Some (YP09.mkRegion (Some 19%nat) 0 (fs_frame_bytes 3 / 8) 0 (fs_frame_bytes 3 / 8) crtB_sh12) /\
  sr_get (ss_regs ssC) 10%bv = SOff 26 0 /\
  (forall q, In q [18; 19; 20; 21; 22; 23; 24; 25; 26]%nat -> sr_get (ss_regs ssC) (Z_to_bv 5 (Z.of_nat q)) = SOff q 0) /\
  sr_get (ss_regs ssC) (Z_to_bv 5 (Z.of_nat 27)) = SOff 47 0x1a0.
Lemma crtB_site12_of : forall ssC,
  crtB_csite_w ssC A_pj_object 0x82124 crtB_csF12 ->
  nth_error (ss_mem ssC) 3 =
    Some (YP09.mkRegion (Some 19%nat) 0 (fs_frame_bytes 3 / 8) 0 (fs_frame_bytes 3 / 8) crtB_sh12) ->
  forallb (fun q => sv_eqb (sr_get (ss_regs ssC) (Z_to_bv 5 (Z.of_nat q))) (SOff q 0)) [18; 19; 20; 21; 22; 23; 24; 25; 26]%nat
    = true ->
  sr_get (ss_regs ssC) 10%bv = SOff 26 0 -> sr_get (ss_regs ssC) (Z_to_bv 5 (Z.of_nat 27)) = SOff 47 0x1a0 ->
  crtB_site12 ssC.
Proof.
intros ssC H1 H2 H3 H4 H5. split; [exact H1|]. split; [exact H2|]. split; [exact H4|]. split; [|exact H5].
intros q Hq. rewrite forallb_forall in H3. specialize (H3 q Hq). apply sv_eqb_eq in H3. exact H3.
Qed.
Lemma crtB_site12_ok : crtB_site12 crtB_sc12 /\ crtB_site12 crtB_sc12z.
Proof.
split; apply crtB_site12_of; try (vm_compute; reflexivity);
  (unfold crtB_csite_w; repeat split; try (vm_compute; reflexivity); right; left; reflexivity).
Qed.
Lemma crtB_sh12_in : forall o i, In o [4; 16; 28; 40] -> 0 <= i < 7 -> In (YP09.mkChunk (o + i) (CVal 1 (SLit 0))) crtB_sh12.
Proof.
intros o i Ho Hi.
assert (Hi' : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6) by lia.
cbn [In] in Ho.
destruct Ho as [<-|[<-|[<-|[<-|[]]]]]; destruct Hi' as [->|[->|[->|[->|[->|[->| ->]]]]]];
  cbv [crtB_sh12]; repeat (first [left; reflexivity | right]).
Qed.
Lemma crtB_sh12_in52 : In (YP09.mkChunk 52 (CVal 1 (SLit 0))) crtB_sh12.
Proof. cbv [crtB_sh12]. repeat (first [left; reflexivity | right]). Qed.
(* the shadow arithmetic of a frame object, with no context *)
Lemma crtB_soa : forall F o i, F mod 8 = 0 -> o mod 8 = 0 ->
  shadow_of_addr SHADOW_OFF (F + o) + i = shadow_addr F + (o / 8 + i).
Proof. intros F o i H1 H2. unfold shadow_of_addr, shadow_addr. Z.div_mod_to_equations. lia. Qed.

Section seg12. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis PJ_OBJECT : @pj_object_spec fx rc SK tfibsegs B.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* a zero chunk of the frame's shadow region reads 0 *)
Lemma crtB_sh_zero : forall E (H : word -> bool) m b cs o,
  region_ok tfibsegs E (mrestrict H m) (YP09.mkRegion (Some 19%nat) 0 (fs_frame_bytes 3 / 8) 0 (fs_frame_bytes 3 / 8) cs) ->
  bv_unsigned (ew E 19) = b -> In (YP09.mkChunk o (CVal 1 (SLit 0))) cs ->
  aview tfibsegs H m (b + o) = Some 0.
Proof.
intros E H m b cs o HR Hb Hin.
pose proof (fsw_field E (mrestrict H m) 19 b cs 0 _ 0 _ o 1 (SLit 0) 0 HR Hb Hin eq_refl ltac:(cbn; lia)
  ltac:(cbn; lia)) as V.
pose proof (V 0%nat ltac:(cbn; lia)) as V0. cbn [Z.of_nat] in V0. rewrite Z.add_0_r in V0.
unfold aview. rewrite V0. reflexivity.
Qed.
(* a stretch of a frame object addressable from the run's zero shadow chunks *)
Lemma crtB_ra12 : forall E (H : word -> bool) m F o len,
  region_ok tfibsegs E (mrestrict H m)
    (YP09.mkRegion (Some 19%nat) 0 (fs_frame_bytes 3 / 8) 0 (fs_frame_bytes 3 / 8) crtB_sh12) ->
  bv_unsigned (ew E 19) = shadow_addr F -> F mod 32 = 0 -> o mod 8 = 0 -> len mod 8 = 0 ->
  (forall i, 0 <= i < len / 8 -> In (YP09.mkChunk (o / 8 + i) (CVal 1 (SLit 0))) crtB_sh12) ->
  range_addressable (aview tfibsegs H m) SHADOW_OFF (F + o) len.
Proof.
intros E H m F o len HR Hb HF Ho Hl Hc.
apply zero_shadow_range; [exact (crtB_m8_add F o HF Ho) | exact Hl |].
intros i Hi. rewrite (crtB_soa F o i (crtB_m8 F HF) Ho).
exact (crtB_sh_zero E H m _ crtB_sh12 _ HR Hb (Hc i Hi)).
Qed.
(* a frame object placed: in the live class-3 frame, 8-aligned, addressable, writable *)
Lemma crtB_pobj_mk : forall ly S U (W : world tfibsegs) m md cx o,
  ARU tfibsegs B ly S U W m md -> In (3, c_pos cx) (frames S) -> frame_addr ly 3 (c_pos cx) = crt_F cx ->
  0 <= o -> o + 56 <= 512 -> o mod 8 = 0 ->
  range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF (crt_F cx + o) 56 ->
  pobj tfibsegs B ly S W m (crt_F cx + o).
Proof.
intros ly S U W m md cx o HARU Hin EF Ho0 Ho1 Ho8 HRA.
set (F := crt_F cx) in *.
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARU) as HAR.
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 (c_pos cx) HAR Hin) as (Hm32 & Happ & Hfp & _).
rewrite EF in Hm32, Happ, Hfp. rewrite crt_frame3 in Happ, Hfp.
destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ 3 (c_pos cx) HAR Hin) as (HF4096 & HFceil & _).
rewrite EF in HF4096. rewrite EF, crt_frame3 in HFceil.
split.
- left. split; [|split].
  + exists 3, (c_pos cx). split; [exact Hin|]. rewrite EF, crt_frame3.
    split; [lia|]. split; [exact (crtB_m8 F Hm32)|]. lia.
  + exact (crtB_m8_add F o Hm32 Ho8).
  + exact HRA.
- intros i Hi. apply (apresent_writable tfibsegs).
  destruct (Hfp (F + o + i) ltac:(lia)) as ((Hh & b & Hb) & _).
  split; [exact Hh|]. exists b.
  rewrite <- (unpoison_app B ly S U W m md (F + o + i) HARU).
  + exact Hb.
  + pose proof (@alloc_ceiling_lt rc) as HC47. change (2 ^ 47) with 140737488355328 in HC47.
    change (2 ^ 64) with 18446744073709551616. lia.
  + cbv [in_app kLowShadowBeg kHighMemBeg] in Happ. cbv [SHADOW_OFF kHighMemBeg]. lia.
Qed.
(* the heap data of the boundary (text's block, its bytes and C string, dec's block and bytes) carried to a memory
   where every live block reads the same: the text's cstr_ok is re-derived (FSH_crt_cstr.crt_cstr_of_rblock) *)
Lemma crtB_heap_keep : forall ly S (W : world tfibsegs) m ly' S' U' (W' : world tfibsegs) m' md' text ntext dec ndec
  (lt ld : list Z),
  ARU tfibsegs B ly' S' U' W' m' md' -> FSupoisonU.fs_heads B ly' S' U' ->
  ablocks B ly' S' = ablocks B ly S ->
  (forall p n i, In (p, n) (ablocks B ly S) -> 0 <= i < req_size n ->
     aview tfibsegs (w_H W') m' (p + i) = aview tfibsegs (w_H W) m (p + i)) ->
  Z.of_nat (length lt) + 1 = ntext -> Z.of_nat (length ld) <= ndec ->
  fs_rblock tfibsegs B ly S W m text ntext -> zbytes_at tfibsegs W m text (lt ++ [0]) -> cstr_ok tfibsegs W m text lt ->
  fs_rblock tfibsegs B ly S W m dec ndec -> zbytes_at tfibsegs W m dec ld ->
  fs_rblock tfibsegs B ly' S' W' m' text ntext /\ zbytes_at tfibsegs W' m' text (lt ++ [0]) /\
  cstr_ok tfibsegs W' m' text lt /\
  fs_rblock tfibsegs B ly' S' W' m' dec ndec /\ zbytes_at tfibsegs W' m' dec ld.
Proof.
intros ly S W m ly' S' U' W' m' md' text ntext dec ndec lt ld HARU' HHD' Eab KB Llt Lld HRT HZT HCT HRD HZD.
assert (RBK : forall p n, fs_rblock tfibsegs B ly S W m p n -> fs_rblock tfibsegs B ly' S' W' m' p n).
{ intros p n (Hp & Hal & Hn & Hv). split; [rewrite Eab; exact Hp|]. split; [exact Hal|]. split; [exact Hn|].
  apply (crtB_val_mem_keep (w_H W) (w_H W') m m' _ 8 _); [|exact Hv].
  intros i Hi. apply (KB _ _ i Hp). pose proof (req_size_pos (n + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hrq).
  unfold HEAD in *. cbn in Hi. lia. }
assert (ZBK : forall p n l, fs_rblock tfibsegs B ly S W m p n -> Z.of_nat (length l) <= n ->
  zbytes_at tfibsegs W m p l -> zbytes_at tfibsegs W' m' p l).
{ intros p n l (Hp & _ & Hn & _) Hl Hz. apply (crtB_garr8_keep (w_H W) (w_H W') m m' p l); [|exact Hz].
  intros i Hi. pose proof (req_size_pos (n + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hrq).
  replace (p + i) with ((p - HEAD) + (HEAD + i)) by lia. apply (KB _ _ _ Hp). unfold HEAD in *. lia. }
assert (Llt' : Z.of_nat (length (lt ++ [0])) <= ntext)
  by (rewrite length_app, Nat2Z.inj_add; cbn [length Z.of_nat]; lia).
pose proof (ZBK _ _ _ HRT Llt' HZT) as HZT'.
pose proof (RBK _ _ HRT) as HRT'.
split; [exact HRT'|]. split; [exact HZT'|].
split.
{ destruct HCT as ((_ & Hnz) & _). pose proof HRT' as (Hp' & Hal' & _).
  apply (crt_cstr_of_rblock B ly' S' U' W' m' md' text lt ntext HARU' HHD' Hp' Hal' Llt HZT').
  intros Hin0. rewrite Forall_forall in Hnz. exact (Hnz 0 Hin0 eq_refl). }
split; [exact (RBK _ _ HRD) | exact (ZBK _ _ _ HRD Lld HZD)].
Qed.
(* a boundary run's write window (the saved words, the s1 slots, the frame and its shadow) holds no image byte and no
   byte of a live block (port of FSH_crt_segD2_s36.v crtD2_w36, a5a8bfb0274, for any boundary pc) *)
Lemma crtB_w_out : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) mem md3 r,
  crt_E cx E ->
  @ajournal rc SK tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 mem) md3 k ->
  ARU tfibsegs B ly3 S3 U3 W3 mem md3 -> frames S3 = (3, c_pos cx) :: frames (c_S cx) ->
  (forall a, in_img tfibsegs a -> ~ in_wrange E (ss_mem (crt_ss_ret r crt_cs1 crt_csF)) a) /\
  (forall q m a, In (q, m) (ablocks B ly3 S3) -> q <= a < q + req_size m ->
     ~ in_wrange E (ss_mem (crt_ss_ret r crt_cs1 crt_csF)) a).
Proof.
intros cx E k ly3 S3 U3 W3 mem md3 r HE HJ HARU Hfr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 YM05.alloc_ceiling_val) as HCV.
destruct crtB_stk13 as (HSTK & HSTK0 & _).
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARU) as HAR.
pose proof HE as (E2 & E3 & E4 & E8 & E9 & E19 & _).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (H16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (H0 : 192 <= spZ (c_regs cx)) by lia.
destruct (crt_sp1_facts cx H16 H0) as (Hsp1b & _ & _).
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfr; left; reflexivity).
pose proof (crt_F_ly cx _ ly3 Hly) as EF.
destruct (frames_bounds tfibsegs B LAWS ly3 S3 W3 _ md3 3 (c_pos cx) HAR Hin3) as (HF0 & HFc & _).
rewrite EF in HF0, HFc. rewrite crt_frame3 in HFc.
assert (HFrng : 0 <= crt_F cx < kHighMemEnd) by (rewrite C4; lia).
pose proof (shadow_addr_bounds (crt_F cx) HFrng) as (HS1b & HS2b).
pose proof (shadow_addr_bounds (crt_F cx + 511) ltac:(rewrite C4; lia)) as (_ & HS3b).
assert (HSFlo : 2147450880 <= crt_SF cx) by (unfold crt_SF; rewrite C5 in HS1b; lia).
assert (HSF64 : crt_SF cx + 64 <= shadow_addr (crt_F cx + 511) + 1)
  by (unfold crt_SF, shadow_addr; Z.div_mod_to_equations; lia).
assert (HSFhi : crt_SF cx + 64 <= 17594333495296) by (rewrite C2 in HS3b; lia).
assert (E47 : bv_unsigned (ew E 47) = crt_F cx) by (rewrite (crt_E_F cx E HE); apply wz; lia).
assert (RG : forall a, in_wrange E (ss_mem (crt_ss_ret r crt_cs1 crt_csF)) a ->
  (spZ (c_regs cx) - 104 <= a < spZ (c_regs cx)) \/ (crt_sp1 cx + 16 <= a < crt_sp1 cx + 88) \/
  (crt_F cx <= a < crt_F cx + 512) \/ (crt_SF cx <= a < crt_SF cx + 64)).
{ intros a (rg & Hr & Hra).
  unfold crt_ss_ret, fss_ret_s0_args, fss_ret_s0_regs, crt_ret_regions in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | []]]]];
    unfold fs_ret_s0_region, crt_slot_region, crt_frame_region, crt_shadow_region in Hra;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra.
  - rewrite E8 in Hra. left. lia.
  - rewrite E9 in Hra. right. left. lia.
  - rewrite E47, crt_frame3 in Hra. right. right. left. lia.
  - rewrite E19, crt_frame3 in Hra. change (512 / 8) with 64 in Hra. right. right. right. lia. }
split.
- intros a Ha Hw. pose proof (FSH_crt_segD.crt_img_range a Ha) as Hai.
  destruct (RG a Hw) as [Hr | [Hr | [Hr | Hr]]]; [lia | lia | | lia].
  exact (frm_img tfibsegs B LAWS ly3 S3 W3 _ md3 3 (c_pos cx) a HAR Hin3 ltac:(rewrite EF, crt_frame3; lia) Ha).
- intros q m a Hq Ha Hw.
  destruct (fsw_ablock_low B ly3 S3 W3 _ md3 q m HAR Hq) as (Hq4096 & Hqc & _).
  destruct (RG a Hw) as [Hr | [Hr | [Hr | Hr]]]; [lia | lia | |].
  + pose proof (sep_block_frame tfibsegs B LAWS ly3 S3 W3 _ md3 q m 3 (c_pos cx) HAR Hq Hin3) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. rewrite EF, crt_frame3 in D. lia.
  + apply (fsw_ablock_off_shadow B ly3 S3 W3 _ md3 q m HAR Hq a Ha). unfold SHADOW_OFF.
    change (2 ^ 44) with 17592186044416. lia.
Qed.

(* ---- segment 12's callee part, at either call-site state: the boundary's heap data through the run (crtB_w_out) and
   across pj_object (doc); the four objects placed from the run's shadow stores, the n cell from its zero store ---- *)
Lemma crtB_hcall12 : forall r0 ssC, crtB_site12 ssC ->
  crtB_hcall_w SK B (crt_ss_ret r0 crt_cs1 crt_csF) ssC A_pj_object 0x82124 STK_pj_object
    (crtB_INV_820a0 B) (crtB_INV_82124 B).
Proof.
intros r0 ssC HSITE.
intros cx E k ly3 S3 U3 W3 ms3 md3 regsC memC mdC HB HE HINV HJC HARUC Hfr HF HFr HSC RG HPRE HFRL HTOP.
destruct HSITE as ((_ & _ & _ & _ & M2 & _ & _ & G2 & _) & M3 & H10 & HSV & H27).
destruct HINV as (E18 & E20 & E21 & E22 & E23 & E26 & same & nsame & dec & live & peak & cnt & E24 & E25 &
  HPB & HPU & HHD & HRT & HZT & HCT & HRD & HZD & HGL & HLV & HBB & HCN & HK).
set (F := crt_F cx) in *.
pose proof HE as (E2 & _ & _ & _ & _ & E19 & _).
pose proof HJC as (HAR3 & Hly3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct crtB_stk13 as (STKo & STK0 & STK1).
assert (Hsp0 : alloc_ceiling + STK_check_round_trip <= spZ (c_regs cx)) by lia.
assert (EF : frame_addr ly3 3 (c_pos cx) = F) by exact (crt_F_ly cx _ ly3 Hly3).
assert (Hin : In (3, c_pos cx) (frames S3)) by (rewrite Hfr; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ 3 (c_pos cx) HAR3 Hin) as (HF4096 & HFceil & _).
rewrite EF in HF4096. rewrite EF, crt_frame3 in HFceil.
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 (c_pos cx) HAR3 Hin) as (Hm32 & Happ & _).
rewrite EF in Hm32, Happ. rewrite crt_frame3 in Happ.
destruct (crt_sp1_facts cx Hal16 ltac:(lia)) as (Hsp1 & _ & _).
assert (Esp : spZ regsC = crt_sp1 cx) by (unfold spZ; rewrite RG, G2, fsw_SOff0; exact E2).
pose proof (@alloc_ceiling_lt rc) as HC47. change (2 ^ 47) with 140737488355328 in HC47.
assert (HFv : bv_unsigned (ew E 47) = F)
  by (rewrite (crt_E_F cx E HE); apply wz; change (2 ^ 64) with 18446744073709551616; lia).
(* the boundary's heap data reach the call memory: the run's windows hold no image byte and no block byte *)
destruct (crtB_w_out cx E k ly3 S3 U3 W3 memC mdC r0 HE HJC HARUC Hfr) as (NWI & NWB).
assert (KI : forall a, in_img tfibsegs a -> aview tfibsegs (w_H W3) memC a = aview tfibsegs (w_H W3) (ms_mem ms3) a)
  by exact (FSH_crt_segD.crt_img_frame E _ _ _ _ HFr NWI).
assert (KB0 : forall p n i, In (p, n) (ablocks B ly3 S3) -> 0 <= i < req_size n ->
  aview tfibsegs (w_H W3) memC (p + i) = aview tfibsegs (w_H W3) (ms_mem ms3) (p + i)).
{ intros p n i Hp Hi. destruct (fsw_ablock_low B ly3 S3 W3 _ mdC p n HAR3 Hp) as (Hp0 & Hpc & _).
  apply aview_eq_of. apply HFr. rewrite (wz (p + i)) by (change (2 ^ 64) with 18446744073709551616; lia).
  exact (NWB p n (p + i) Hp ltac:(lia)). }
pose proof (FSH_crt_segD.crt_glob_keep W3 (ms_mem ms3) memC live peak cnt SIZE_MAXZ KI HGL) as HGLc.
assert (Ltxt := crtB_len_text (c_bs cx)). assert (Ldec := crtB_len_dec (c_bs cx)).
assert (Llt : Z.of_nat (length (WriterSpec.b64_enc (c_bs cx))) + 1 = FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))))
  by (rewrite length_app, Nat2Z.inj_add in Ltxt; cbn [length Z.of_nat] in Ltxt; lia).
destruct (crtB_heap_keep ly3 S3 W3 (ms_mem ms3) ly3 S3 U3 W3 memC mdC (c_text cx) _ dec _
  (WriterSpec.b64_enc (c_bs cx)) (c_bs cx) HARUC HHD eq_refl KB0 Llt Ldec HRT HZT HCT HRD HZD)
  as (HRTc & HZTc & HCTc & HRDc & HZDc).
(* the frame objects at the call: the run's 29 shadow stores, and the n cell *)
assert (HR3 : region_ok tfibsegs E (mrestrict (w_H W3) memC)
    (YP09.mkRegion (Some 19%nat) 0 (fs_frame_bytes 3 / 8) 0 (fs_frame_bytes 3 / 8) crtB_sh12))
  by exact (fsw_region_nth E ssC _ 3 _ HSC M3).
assert (HR2 : region_ok tfibsegs E (mrestrict (w_H W3) memC) (crt_frame_region crtB_csF12))
  by exact (fsw_region_nth E ssC _ 2 _ HSC M2).
assert (E19' : bv_unsigned (ew E 19) = shadow_addr F) by exact E19.
assert (HRAo : forall o, In (o / 8) [4; 16; 28; 40] -> o mod 8 = 0 ->
  range_addressable (aview tfibsegs (w_H W3) memC) SHADOW_OFF (F + o) 56).
{ intros o Ho Ho8. apply (crtB_ra12 E (w_H W3) memC F o 56 HR3 E19' Hm32 Ho8 eq_refl).
  intros i Hi. change (56 / 8) with 7 in Hi. exact (crtB_sh12_in _ i Ho Hi). }
assert (HPd : pobj tfibsegs B ly3 S3 W3 memC (F + 0x20)).
{ apply (crtB_pobj_mk ly3 S3 U3 W3 memC mdC cx 0x20 HARUC Hin EF); [lia | lia | reflexivity |].
  apply HRAo; [left; reflexivity | reflexivity]. }
assert (HVN0 : val_mem tfibsegs (mrestrict (w_H W3) memC) (F + 0x1a0) 8 0).
{ exact (fsw_field E (mrestrict (w_H W3) memC) 47 F crtB_csF12 0 (fs_frame_bytes 3) 0 (fs_frame_bytes 3)
    416 8 (SLit 0) 0 HR2 HFv ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). }
assert (HRN0 : range_addressable (aview tfibsegs (w_H W3) memC) SHADOW_OFF (F + 0x1a0) 8).
{ apply (crtB_ra12 E (w_H W3) memC F 0x1a0 8 HR3 E19' Hm32 eq_refl eq_refl).
  intros i Hi. change (8 / 8) with 1 in Hi. assert (i = 0) as -> by lia. exact crtB_sh12_in52. }
(* pj_object (doc) *)
assert (R10 : YK11.getr regsC 10%bv = w64 (F + 0x20)) by (rewrite RG, H10, fsw_SOff0, E26; reflexivity).
pose proof (PJ_OBJECT ly3 S3 U3 W3 regsC memC mdC (crt_ch1 cx) (F + 0x20) live peak cnt SIZE_MAXZ HPRE HHD R10 HPd
  ltac:(left; rewrite Esp; lia) HGLc) as HC.
exists [(F + 0x20, F + 0x20 + 56)], 0. eexists. split; [exact HC|].
split.
{ intros a (rr & [<-|[]] & Ha). cbn [fst snd] in Ha. right; right; right; left. unfold in_frames. exists 3, (c_pos cx).
  split; [left; reflexivity|]. left. unfold in_zr, frame_rng; cbn [fst snd]. rewrite EF, crt_frame3. lia. }
split.
{ intros a Ha (rr & [<-|[]] & Hr). cbn [fst snd] in Hr. rewrite crt_frame3 in Ha. lia. }
intros W' c' HP.
destruct HP as (ly' & S' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HPr & HQ).
exists ly', S', U3, regs', mem', md'.
split; [exact Ec|]. split; [exact HJc|]. split; [exact OK'|]. split; [exact PO'|]. split; [exact HPr|].
intros HJ' HARU'.
destruct HQ as (Eab & HRTs & HPd2 & HGL2).
pose proof HJc as (HARc & Hlyc & _ & _ & _ & Hfrc & _).
set (FPc := [(F + 0x20, F + 0x20 + 56)]).
assert (NF : forall a, (a < F + 0x20 \/ F + 0x20 + 56 <= a) -> ~ inFP FPc a)
  by (intros a Ha (rr & [<-|[]] & Hr); cbn [fst snd] in Hr; lia).
assert (KB : forall p n i, In (p, n) (ablocks B ly3 S3) -> 0 <= i < req_size n ->
  aview tfibsegs (w_H W') mem' (p + i) = aview tfibsegs (w_H W3) memC (p + i)).
{ intros p n i Hp Hi. apply (crt_keep_blk SK B ly3 S3 U3 W3 memC mdC ly' S' U3 W' mem' md' STK_pj_object (spZ regsC)
    FPc 0 p n i HARUC HARU' HJc Hp ltac:(rewrite Eab; exact Hp) Hi).
  apply NF. pose proof (sep_block_frame tfibsegs B LAWS _ _ _ _ _ p n 3 (c_pos cx) HAR3 Hp Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EF, crt_frame3 in Hd. lia. }
assert (KF : forall a, F <= a < F + 512 -> (a < F + 0x20 \/ F + 0x20 + 56 <= a) ->
  aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W3) memC a).
{ intros a Ha Hn. apply (crt_keep_frm SK B ly3 S3 U3 W3 memC mdC ly' S' U3 W' mem' md' STK_pj_object (spZ regsC)
    FPc 0 3 (c_pos cx) a HARUC HARU' HJc Hin); [unfold in_zr, frame_rng; cbn [fst snd]; rewrite EF, crt_frame3; lia|].
  exact (NF a Hn). }
(* the boundary registers after the call: pj_object keeps s2 .. s11 *)
assert (KRg : forall (n : nat) (v : sv), (18 <= n <= 27)%nat ->
  sr_get (ss_regs ssC) (Z_to_bv 5 (Z.of_nat n)) = v -> ew (Ereg regs' (crt_extra cx)) n = sv_denot E v).
{ intros n v Hn Hs.
  assert (Hu : Z.of_nat n = bv_unsigned (Z_to_bv 5 (Z.of_nat n))).
  { rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity | change (bv_modulus 5) with 32; lia]. }
  rewrite (ew_Ereg_nat regs' (crt_extra cx) n (Z_to_bv 5 (Z.of_nat n)) Hu).
  rewrite (HPr (Z.of_nat n) ltac:(unfold acallee_saved; lia)), RG, Hs. reflexivity. }
assert (KR : forall n : nat, In n [18; 19; 20; 21; 22; 23; 24; 25; 26]%nat ->
  ew (Ereg regs' (crt_extra cx)) n = ew E n).
{ intros n Hn. rewrite (KRg n (SOff n 0) ltac:(cbn [In] in Hn; lia) (HSV n Hn)). apply fsw_SOff0. }
assert (G27 : ew (Ereg regs' (crt_extra cx)) 27 = Z_to_bv 64 (F + 0x1a0)).
{ rewrite (KRg 27%nat _ ltac:(lia) H27).
  apply bv_eq. rewrite denot_SOff, HFv.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64);
    change (2 ^ 64) with 18446744073709551616; lia).
  apply zcanon_id. unfold M64. change (2 ^ 64) with 18446744073709551616. lia. }
unfold crtB_INV_82124. lazy zeta beta. cbn [ms_mem mkst]. fold F.
rewrite (KR 18%nat ltac:(cbn; tauto)), (KR 20%nat ltac:(cbn; tauto)), (KR 21%nat ltac:(cbn; tauto)),
  (KR 22%nat ltac:(cbn; tauto)), (KR 23%nat ltac:(cbn; tauto)), (KR 26%nat ltac:(cbn; tauto)), G27.
split; [exact E18|]. split; [exact E20|]. split; [exact E21|]. split; [exact E22|]. split; [exact E23|].
split; [exact E26|]. split; [reflexivity|].
exists same, nsame, dec, live, peak, cnt.
rewrite (KR 24%nat ltac:(cbn; tauto)), (KR 25%nat ltac:(cbn; tauto)).
split; [exact E24|]. split; [exact E25|].
split; [rewrite Eab; exact HPB|]. split; [exact HPU|].
assert (HHD' : FSupoisonU.fs_heads B ly' S' U3) by (intros r Hr; rewrite Eab; exact (HHD r Hr)).
split; [exact HHD'|].
destruct (crtB_heap_keep ly3 S3 W3 memC ly' S' U3 W' mem' md' (c_text cx) _ dec _
  (WriterSpec.b64_enc (c_bs cx)) (c_bs cx) HARU' HHD' Eab KB Llt Ldec HRTc HZTc HCTc HRDc HZDc)
  as (HRT' & HZT' & HCT' & HRD' & HZD').
split; [exact HRT'|]. split; [exact HZT'|]. split; [exact HCT'|]. split; [exact HRD'|]. split; [exact HZD'|].
split; [exact HRTs|].
split; [exact (crtB_obj0_hdr B ly' S' W' mem' (F + 0x20) HRTs)|].
(* the four objects' placements after the call *)
assert (Hin' : In (3, c_pos cx) (frames S')) by (rewrite Hfrc; exact Hin).
assert (EF' : frame_addr ly' 3 (c_pos cx) = F).
{ rewrite <- EF. unfold frame_addr. destruct Hlyc as (_ & _ & _ & _ & _ & EFl & _). rewrite EFl. reflexivity. }
assert (SHO : forall x, F <= x < F + 512 -> ~ inFP FPc (shadow_addr x)).
{ intros x Hx (rr & [<-|[]] & Hr). cbn [fst snd] in Hr. cbv [in_app kLowShadowBeg kHighMemBeg] in Happ.
  apply (crtB_sh_out F x (F + 0x20) (F + 0x20 + 56)); [lia | | lia | lia | lia | exact Hr].
  destruct Happ as (_ & [Ha | (Ha1 & Ha2)]); [left; exact Ha | right; split; [exact Ha1 | exact HFceil]]. }
assert (RAK : forall o len, 0 <= o -> o + len <= 512 -> o mod 8 = 0 ->
  range_addressable (aview tfibsegs (w_H W3) memC) SHADOW_OFF (F + o) len ->
  range_addressable (aview tfibsegs (w_H W') mem') SHADOW_OFF (F + o) len).
{ intros o len Ho0 Ho1 Ho8 HRA.
  apply (crtB_RA_keep_frm SK B ly3 S3 U3 W3 memC mdC ly' S' U3 W' mem' md' STK_pj_object (spZ regsC) FPc 0 3
    (c_pos cx) (F + o) len HARUC HARU' HJc Hin); [rewrite EF; exact (crtB_m8 F Hm32) | reflexivity
    | rewrite EF; lia | rewrite EF, crt_frame3; lia | | exact HRA].
  intros x Hx. apply SHO. lia. }
assert (POK : forall o, In (o / 8) [4; 16; 28; 40] -> 0 <= o -> o + 56 <= 512 -> o mod 8 = 0 ->
  pobj tfibsegs B ly' S' W' mem' (F + o)).
{ intros o Ho Ho0 Ho1 Ho8. apply (crtB_pobj_mk ly' S' U3 W' mem' md' cx o HARU' Hin' EF' Ho0 Ho1 Ho8).
  exact (RAK o 56 Ho0 Ho1 Ho8 (HRAo o Ho Ho8)). }
split; [exact HPd2|].
split; [exact (POK 0x80 ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia) eq_refl)|].
split; [exact (POK 0xe0 ltac:(right; right; left; reflexivity) ltac:(lia) ltac:(lia) eq_refl)|].
split; [exact (POK 0x140 ltac:(right; right; right; left; reflexivity) ltac:(lia) ltac:(lia) eq_refl)|].
(* the n cell and its shadow *)
split.
{ apply (crtB_val_mem_keep (w_H W3) (w_H W') memC mem' _ 8 _); [|exact HVN0].
  intros i Hi. cbn in Hi. apply KF; lia. }
split; [exact (RAK 0x1a0 8 ltac:(lia) ltac:(lia) eq_refl HRN0)|].
split; [exact HGL2|]. split; [exact HLV|].
split; [rewrite (blocks_bytes_bsum B ly' S'), Eab, <- (blocks_bytes_bsum B ly3 S3); exact HBB|].
split; [exact HCN | lia].
Qed.

Lemma crtB_hcall_w_mono : forall ss0 ssC A_c r STKc (INV1 INV2 INV' : crt_inv),
  (forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3,
     INV1 cx E k ly3 S3 U3 W3 ms3 md3 -> INV2 cx E k ly3 S3 U3 W3 ms3 md3) ->
  crtB_hcall_w SK B ss0 ssC A_c r STKc INV2 INV' -> crtB_hcall_w SK B ss0 ssC A_c r STKc INV1 INV'.
Proof.
intros ss0 ssC A_c r STKc INV1 INV2 INV' HI H.
intros cx E k ly3 S3 U3 W3 ms3 md3 regsC memC mdC HB HE HINV.
exact (H cx E k ly3 S3 U3 W3 ms3 md3 regsC memC mdC HB HE (HI _ _ _ _ _ _ _ _ _ HINV)).
Qed.

(* SEGMENT 12, |bs| > 0: 0x8209c (`bnez a0`, a0 = 0) -> pj_object (doc) -> 0x82124 *)
Lemma crtB_seg12 :
  crt_from SK B (crt_ss_ret 0x82124 crt_cs1 crt_csF) (crtB_INV_82124 B) ->
  crt_from SK B crtB_ss_8209c (crtB_INV_8209c B).
Proof.
intros NEXT. destruct crtB_site12_ok as (HS12 & _).
exact (crtB_seg_call_brw SK B 0x8209c A_pj_object 0x82124 crtB_sb12 crtB_sc12 crtB_csF12 _ _ STK_pj_object
  crtB_br12 crtB_run12 crtB_mem12 (proj1 HS12) ltac:(change (2 ^ 64) with 18446744073709551616; lia) eq_refl
  (proj1 (proj2 crtB_stk13)) (proj1 crtB_stk13)
  (fun cx E k ly3 S3 U3 W3 ms3 md3 H => proj1 H)
  (crtB_hcall_w_mono _ _ _ _ _ (crtB_INV_8209c B) (crtB_INV_820a0 B) _
     (fun cx E k ly3 S3 U3 W3 ms3 md3 H => proj2 H) (crtB_hcall12 0x8209c crtB_sc12 HS12))
  NEXT).
Qed.
(* SEGMENT 12, |bs| = 0: 0x820a0 -> pj_object (doc) -> 0x82124 *)
Lemma crtB_seg12z :
  crt_from SK B (crt_ss_ret 0x82124 crt_cs1 crt_csF) (crtB_INV_82124 B) ->
  crt_from SK B crtB_ss_820a0 (crtB_INV_820a0 B).
Proof.
intros NEXT. destruct crtB_site12_ok as (_ & HS12z).
exact (crtB_seg_call_w SK B 0x820a0 A_pj_object 0x82124 crtB_sc12z crtB_csF12 _ _ STK_pj_object
  crtB_run12z (proj1 HS12z) ltac:(change (2 ^ 64) with 18446744073709551616; lia) eq_refl
  (proj1 (proj2 crtB_stk13)) (proj1 crtB_stk13) (crtB_hcall12 0x820a0 crtB_sc12z HS12z) NEXT).
Qed.
End seg12.

(* ================= lane B1's back half: from the bcmp-return boundary to crt_INV_8212c (segments 12 + 13) ========= *)
Section b1. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis PJ_OBJECT : @pj_object_spec fx rc SK tfibsegs B.
Lemma crtB_from_8209c :
  crt_from SK B (crt_ss_ret 0x8212c crt_cs1 crt_csF) (crt_INV_8212c B) -> crt_from SK B crtB_ss_8209c (crtB_INV_8209c B).
Proof. intros H. exact (crtB_seg12 SK B PJ_OBJECT (crtB_seg13 SK B PJ_OBJECT H)). Qed.
Lemma crtB_from_820a0 :
  crt_from SK B (crt_ss_ret 0x8212c crt_cs1 crt_csF) (crt_INV_8212c B) -> crt_from SK B crtB_ss_820a0 (crtB_INV_820a0 B).
Proof. intros H. exact (crtB_seg12z SK B PJ_OBJECT (crtB_seg13 SK B PJ_OBJECT H)). Qed.
End b1.
