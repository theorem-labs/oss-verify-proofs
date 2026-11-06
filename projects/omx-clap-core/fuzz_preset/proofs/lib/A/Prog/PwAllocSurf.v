(* fuzz_preset image A' (asan, #102 pin 1be0f53d96cb, unstripped twin bff8519bbe3e): the walks of alloc.c's five
   accessors of the test harness's allocator statics (alloc.c :129-152) against the texts (lib/A/PRH_FnAlloc.v:70-124,
   blob 83fe93bc86e2, kit of record walkkit-next decff67d721f):
   fuzz_alloc_live_holds, fuzz_alloc_peak_holds, fuzz_alloc_peak_reset_holds, fuzz_alloc_count_holds and
   fuzz_alloc_fail_holds. Every conclusion is SRr (srealizes, YA0n.v).
   RELOCATED 2026-10-29 from the old-pin walks (origin/cold/h-w6rep-2-allocsurf c47ea1638ed6, this file blob
   3e57698d78f7, image d83eb25d / twin f0d2e8d4). The five bodies are instruction-equal mod pc-relative fields on the two
   asan pins (the old d83eb25d, twin f0d2e8d4, and #102's 1be0f53d96cb, twin bff8519bbe3e: 0 real differences;
   every pc-relative target is the same symbol + offset on both pins); this file names no address, so only the
   image changed under it.
   Two text changes from the donor's kit are closed here: (i) the ledger carries #102's two cells as fields
   (PRH_Base.v prh_glob / prh_ledger take `most own`: prh_most and prh_own are conjuncts of prh_glob), so a reader
   keeps them by keeping memory and a writer by keeping them off its cell (pas_glob_keep); (ii) prh_pst has seven
   cells (g_most, g_own_ran_out added), so PST_sep gives 21 disjointness facts (pas_sep7).
   Listings (neutral, h-w6rep-2's allocsurf-dis directory; MEASURED on f0d2e8d4, equal mod pc-relative
   fields on bff8519bbe3e):
     fuzz_alloc_live        auipc a0 ; ld a0 <- g_live ; ret                                            (3 words)
     fuzz_alloc_peak        auipc a0 ; ld a0 <- g_peak ; ret                                            (3 words)
     fuzz_alloc_peak_reset  auipc a0 ; ld a0 <- g_live ; auipc a1 ; sd a0 -> g_peak ; ret               (5 words)
     fuzz_alloc_count       auipc a0 ; ld a0 <- g_count ; ret                                           (3 words)
     fuzz_alloc_fail        auipc a1 ; ld a1 <- g_count ; add a0,a1,a0 ; sltu a1,a0,a1 ; neg a1,a1 ;
                            or a0,a1,a0 ; auipc a1 ; sd a0 -> g_fail_at ; ret                           (9 words)
   The walks read these words from the image (build_table over the segments), so a different body fails them. None
   makes an instrumented access: the readers load a static, the writers store into a static, which is PST.
   Shape (h-hpreset-7's split; origin/cold/h-hpreset-7-walk-S8b b8cc8ce5f57 ExUtf8.v / ExUtf8W.v / lib/B ExUtf8B.v):
   1. pas_rd_run / pas_wr_run state a byte run as machine behaviour over ANY segments (no journal, no ledger);
   2. the cores pas_<fn>_core, parametric in the image ({PI : PrhImg} {PA : PAImg L}) and in the allocator relation
      ARx, build fpost (YCbqG's apost_base_x at PST := prh_pst) from the byte run: a reader by ajournal_x_init and
      ajournal_x_materialize (memory unchanged, the ledger as it was), a writer by ajournal_x_pst_write (the one static
      cell it writes is PST) and S1Ledger.v's prh_ledger_frame (Lam, Hp and the blocks unchanged). Their image facts
      are section hypotheses: YCbqG's PST_ok at prh_pst, PST_sep (the seven statics are pairwise disjoint, so a write
      of one keeps the others) and PST_al (each static is an 8-aligned cell of at most 8 bytes: with cf_head_al it
      puts every head word of the ledger's blocks off the written cell, with no `8 <= cf_head` premise);
   3. image A' (PI_prog_A, prh_img_A at the #102 pins): the five byte runs by the engine (srr_run_with / pas_run_hid,
      then SRr_ret_at) over PI_prog_A's
      segments, and the image facts of prh_img_A's statics by computation (S1ImgA.v's checkers copied; S1ImgA.v is
      not Required);
   4. the five texts at PA := PI_prog_A, PI := prh_img_A, cp := CfParams_preset, ARx := FuzzStrdup.v's ARcf /\
      xs_placed_cf. LAWS is the allocator laws' lift (h-mani-a8's AR_laws_ok_cf -> YGcallcf.v's AR_laws_x_xs, as
      FuzzStrdup.v:234-235 cites it). Opened hypothesis: PST_unowned (PST_ok's B half).
   fuzz_alloc_fail's saturating sum is pas_sat: s = (c + k) mod 2 ^ 64, and s | -(s <u c) is the text's
   `if k <? SIZE_MAXZ - c then c + k else SIZE_MAXZ` in all three cases (no wrap; c + k = SIZE_MAX, no wrap; wrap).
   Mechanics from lib/A/Prog/PwLive.v (the reader, old vocabulary), PwRanOutReset.v (a one-static writer) and PwBase.v
   (pw_rcell / pw_wcell / region_ok_pw_rcell / region_ok_pw_wcell, over AB1v.tfibsegs, the same term as Img0.rsegs).
   No released plain / UBSan file (lib/Prog/fuzz_alloc_*.v, lib/U/Prog) is Required or cited.
   NUMERALS: no ADDRESS literal (the statics are prh_img_A's pi_g_* / pi_gz_*, the entries A_prog_sigma AS_<fn> =
   pa_sigma of PI_prog_A); 3, 5, 9 LENGTH (the listings' word counts); 8 LENGTH (a word's bytes: the width bound and
   the alignment of a static, the stored chunk's width); 32 DERIVED (the symbolic engine's first extra atom, the
   static read); 1, 10 DERIVED (the ISA's register numbers of ra and a0); 64 and 2 ^ 64 WORD (the machine word's
   width and modulus; 2 ^ 64 - 1 is SIZE_MAX); 0, 1 WORD (an absolute region's base, SLit 0, the carry bit); 1 is also
   LENGTH (the one-byte writability window of seg_win_wview). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YI16 YM05 YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP YP08 YL0b.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG0ncf YG0dcf YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
Img0 Listing_prog PAImg_prog PRH_Base PRH_Img PRH_FnAlloc CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PwBase S1Ledger.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
(* YGcallcf's import chain loads Reusable/YF0v.v, whose line 16 sets zify's euclidean-division flag to false
   GLOBALLY; the alignment arguments below (pas_head_off: a mod 16 = 0, 8-aligned statics) need lia's mod / div
   support, so this file sets the flag back to the Stdlib default for itself only *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ==== 1. the byte runs, as machine behaviour over any segments (no journal, no ledger) ==== *)
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.

(* a reader: from pc, back at ra with a0 = the n-byte static at g, memory unchanged, callee-saved kept *)
Definition pas_rd_run (pc g : Z) (n : nat) : Prop :=
  forall (W : world segs) regs mem md v (Q : world segs -> config -> Prop),
  YK0s.ret_ok (YK11.getr regs 1) ->
  val_mem segs (mrestrict (w_H W) mem) g n v -> 0 <= v < 2 ^ 64 ->
  (forall regs' X, getr regs' 10 = w64 v -> aregs_preserved regs regs' ->
     Q W (mkCfg (YK11.mkst regs' (YK11.getr regs 1) mem (YK11.seg_rom segs)) (with_vm_backing (m_vm_lazy md) X md))) ->
  SRr segs W (cfg_at segs pc regs mem md) Q.

(* a writer: reads the ns-byte static at gs (value v), with a0 the entry value of register a0; back at ra with the
   nd-byte static at gd holding f v a0, every other visible byte unchanged, the hidden bytes unchanged, callee-saved
   kept *)
Definition pas_wr_run (pc gs : Z) (ns : nat) (gd : Z) (nd : nat) (f : Z -> Z -> Z) : Prop :=
  forall (W : world segs) regs mem md v a0 (Q : world segs -> config -> Prop),
  YK0s.ret_ok (YK11.getr regs 1) -> getr regs 10 = w64 a0 -> 0 <= a0 < 2 ^ 64 ->
  val_mem segs (mrestrict (w_H W) mem) gs ns v -> 0 <= v < 2 ^ 64 ->
  (forall regs' mem' X, aregs_preserved regs regs' ->
     (forall x : word, ~ (gd <= bv_unsigned x < gd + Z.of_nat nd) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
     mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
     (forall x : word, w_H W x = true -> mem' x = mem x) ->
     val_mem segs (mrestrict (w_H W) mem') gd nd (f v a0) ->
     Q W (mkCfg (YK11.mkst regs' (YK11.getr regs 1) mem' (YK11.seg_rom segs)) (with_vm_backing (m_vm_lazy md) X md))) ->
  SRr segs W (cfg_at segs pc regs mem md) Q.

(* the engine's run (YA0o.v SRr_run_gen) with the growth of the visible memory and the hidden bytes exposed, as
   YCbqG.v SRr_chain_AJx_pst reads them off the unrestricted state *)
Lemma pas_run_hid : forall tbl, table_ok segs tbl -> wx_segs_nowrap segs ->
  forall W n E ss ss' st ms model Q,
  st_ok segs E ss (restrict (w_H W) ms) -> sym_runN segs tbl n ss = (ss', st) ->
  match st with RS_ecall => False | _ => True end ->
  (forall ms' mat', st_ok segs E ss' (restrict (w_H W) ms') ->
     frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     (forall x, w_H W x = true -> ms_mem ms' x = ms_mem ms x) ->
     SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy model) mat' model)) Q) ->
  SRr segs W (mkCfg ms model) Q.
Proof.
intros tbl Htb Hwx W n E ss ss' st ms model Q HS Hrun Hst Hk.
destruct (msteps_run_gen segs tbl Htb n E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
apply (SRr_msteps segs Hwx W ms msr' model Q Hms).
intros model' Hsame Hcl. rewrite (same_but_materialized_wvb model model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model')).
- rewrite Hrr. destruct st; [exact HS' | destruct Hst | exact HS'].
- rewrite Hmm. exact Hfr.
- rewrite Hmm. exact Hgr.
- intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
Qed.
End r.

(* ==== 2. pure facts ==== *)
(* the 21 pairs of prh_pst's seven cells (#102: g_live, g_peak, g_count, g_fail_at, g_ran_out, g_most,
   g_own_ran_out), in order (1,2) (1,3) .. (1,7) (2,3) .. (6,7) *)
Lemma pas_sep7 : forall l1 l2 l3 l4 l5 l6 l7 : Z * Z, YG0f.pairwise zdisjoint [l1; l2; l3; l4; l5; l6; l7] ->
  zdisjoint l1 l2 /\ zdisjoint l1 l3 /\ zdisjoint l1 l4 /\ zdisjoint l1 l5 /\ zdisjoint l1 l6 /\ zdisjoint l1 l7 /\
  zdisjoint l2 l3 /\ zdisjoint l2 l4 /\ zdisjoint l2 l5 /\ zdisjoint l2 l6 /\ zdisjoint l2 l7 /\
  zdisjoint l3 l4 /\ zdisjoint l3 l5 /\ zdisjoint l3 l6 /\ zdisjoint l3 l7 /\
  zdisjoint l4 l5 /\ zdisjoint l4 l6 /\ zdisjoint l4 l7 /\
  zdisjoint l5 l6 /\ zdisjoint l5 l7 /\
  zdisjoint l6 l7.
Proof.
intros l1 l2 l3 l4 l5 l6 l7 H. cbn [YG0f.pairwise] in H. destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & _).
repeat match goal with
| H : Forall _ (_ :: _) |- _ => let a := fresh "A" in pose proof (Forall_inv H) as a; apply Forall_inv_tail in H
end.
repeat split; assumption.
Qed.

(* ==== 3. the cores, parametric in the image ({PI} {PA}): everything but the byte run ==== *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams} {PI : PrhImg} {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
#[local] Abbreviation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variable HL : Z.
Hypothesis LAWS : AR_laws_x segs B ARx HL.
(* YCbqG's PST_ok at PST := prh_pst *)
Hypothesis PST_ok : forall a, Exists (in_zr a) prh_pst -> in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B).
(* the seven statics are pairwise disjoint, and each is an 8-aligned cell of at most one word *)
Hypothesis PST_sep : YG0f.pairwise zdisjoint prh_pst.
Hypothesis PST_al : Forall (fun r => fst r mod 8 = 0 /\ 0 <= snd r <= 8) prh_pst.
(* for the m-form post: each static's bytes are in a writable segment (or in none), and every cell ends below
   TASK_SIZE, so a store to it keeps the kit's memnorm (pas_memnorm_frame below, over YAkMemnorm.memnorm) *)
Hypothesis PST_rw : forall a, Exists (in_zr a) prh_pst ->
  match find_segment segs a 1 with Some seg => seg_writable seg = true | None => True end.
Hypothesis PST_top : forallb (fun r => fst r + snd r <=? TASK_SIZE) prh_pst = true.

Lemma pas_cell_pst : forall g n a, In (g, n) prh_pst -> g <= a < g + n -> Exists (in_zr a) prh_pst.
Proof. intros g n a Hc Ha. apply Exists_exists. exists (g, n). split; [exact Hc | unfold in_zr; cbn [fst snd]; lia]. Qed.

(* a head byte of a ledger block is not a byte of a static: the head word is 8-aligned (a mod 16 = 0, cf_head_al) and
   the static is an 8-aligned cell of at most 8 bytes, so a shared byte makes the head's first byte the static's first
   byte, which PST_ok puts in the image and blk_img_x (it is a block byte) keeps out of it *)
Lemma pas_head_off : forall ly S Hp W mem md Lam peak cnt fail ran most own g n a k i,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (g, Z.of_nat n) prh_pst -> In (a, k) Lam -> 0 <= i < 8 -> ~ (g <= a - cf_head + i < g + Z.of_nat n).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own g n a k i HAR HL0 Hc Hin Hi Hx.
pose proof (proj1 (Forall_forall _ _) PST_al _ Hc) as [Hg8 Hn8]. cbn [fst snd] in Hg8, Hn8.
destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HL0 Hin) as (Hk & Hbl & _ & Ha16 & _).
pose proof (@cf_head_al cp) as Hal. pose proof (@cf_head_nonneg cp) as Hh0.
assert (Eg : a - cf_head = g) by lia.
assert (Hreq : 0 < req_size (k + cf_head)) by (apply prh_req_size_pos; lia).
apply (blk_img_x segs B ARx LAWS ly S Hp W mem md (a - cf_head) (k + cf_head) g HAR Hbl ltac:(lia)).
exact (proj1 (PST_ok g (pas_cell_pst g (Z.of_nat n) g Hc ltac:(lia)))).
Qed.

(* a static off the written cell keeps its value *)
Lemma pas_glob_keep : forall (W : world segs) mem mem' g n g' n' v,
  In (g, Z.of_nat n) prh_pst -> In (g', Z.of_nat n') prh_pst -> zdisjoint (g, Z.of_nat n) (g', Z.of_nat n') ->
  (forall x : word, ~ (g <= bv_unsigned x < g + Z.of_nat n) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  val_mem segs (mrestrict (w_H W) mem) g' n' v -> val_mem segs (mrestrict (w_H W) mem') g' n' v.
Proof.
intros W mem mem' g n g' n' v Hc Hc' Hd Hfr Hv.
apply (prh_val_mem_keep _ _ _ _ _ Hv). intros k Hk.
assert (Hlow : 0 <= g' + Z.of_nat k < kLowMemEnd)
  by (apply pa_segs_low; exact (proj1 (PST_ok _ (pas_cell_pst g' (Z.of_nat n') (g' + Z.of_nat k) Hc' ltac:(lia))))).
apply (prh_mbyte_of_mrestrict (fun z => g <= z < g + Z.of_nat n)); [exact Hfr | unfold kLowMemEnd in Hlow; lia |].
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* the kit's memnorm (YAkMemnorm.v, which PRH_Base's fQmn uses) is kept by a change confined to [lo, hi) below TASK_SIZE
   that puts no byte at a read-only address; YAkMemnorm has this only for a range with no segment (memnorm_frame_off_segs),
   and the statics lie in a writable segment, so the cell form is proved here from the definition *)
Lemma pas_memnorm_frame : forall (sg : list Segment) (m m' : word -> option byte) lo hi,
  YAkMemnorm.memnorm sg m -> (forall x : word, ~ (lo <= bv_unsigned x < hi) -> m' x = m x) -> hi <= TASK_SIZE ->
  (forall (x : word) b, lo <= bv_unsigned x < hi -> m' x = Some b -> YAkMemnorm.ro_addr sg x = false) ->
  YAkMemnorm.memnorm sg m'.
Proof.
intros sg m m' lo hi (Hi & Ht) Hout Hhi Hro. split; intros x b E;
  (destruct (Z_le_dec lo (bv_unsigned x)) as [H1|H1];
   [destruct (Z_lt_dec (bv_unsigned x) hi) as [H2|H2]|]).
- exact (Hro x b (conj H1 H2) E).
- rewrite (Hout x ltac:(lia)) in E. exact (Hi x b E).
- rewrite (Hout x ltac:(lia)) in E. exact (Hi x b E).
- right. lia.
- rewrite (Hout x ltac:(lia)) in E. exact (Ht x b E).
- rewrite (Hout x ltac:(lia)) in E. exact (Ht x b E).
Qed.

(* the post of a reader: memory unchanged, so the journal from entry (materialized) and the ledger as it was (with
   #102's g_most / g_own_ran_out fields, the same most / own) *)
Lemma pas_rd_post : forall STK ly S Hp W regs mem md ch regs' X Lam peak cnt fail ran most own v,
  afn_pre_x segs B ARx STK ly S Hp W regs mem md ch -> aregs_preserved regs regs' -> getr regs' 10 = w64 v ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  fpostm B ARx SK STK [] regs ly S Hp W mem md
    (fun ly' S' Hp' W' regs'' mem' md' => (room_live_cf S -> room_live_cf S') /\ getr regs'' 10 = w64 v /\ Hp' = Hp /\
       S' = S /\ ablocks B ly' S' = ablocks B ly S /\ prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own)
    W (mkCfg (YK11.mkst regs' (YK11.getr regs 1) mem (YK11.seg_rom segs)) (with_vm_backing (m_vm_lazy md) X md)).
Proof.
intros STK ly S Hp W regs mem md ch regs' X Lam peak cnt fail ran most own v HPRE Hpr H10 HL0.
unfold fpostm, fQmn, fpost, apost_base_x.
exists ly, S, Hp, regs', mem, (with_vm_backing (m_vm_lazy md) X md), 0.
split; [reflexivity|].
split; [apply (ajournal_x_materialize segs B prh_pst ARx LAWS pa_segs_low);
        exact (ajournal_x_init (SK := SK) segs B prh_pst ARx STK [] ly S Hp W regs mem md ch HPRE)|].
split; [exact Hpr|].
cbv beta. split; [|exact (fun h => h)].
split; [exact (fun h => h)|]. split; [exact H10|]. split; [reflexivity|]. split; [reflexivity|].
split; [reflexivity|]. exact HL0.
Qed.

(* the post of a writer of ONE static cell (g, n): the journal by ajournal_x_pst_write, the ledger by
   prh_ledger_frame (Lam, Hp, most, own and the blocks unchanged; the heads are off the cell by pas_head_off) *)
Lemma pas_wr_post : forall STK ly S Hp W regs mem md ch regs' mem' X g n Lam peak cnt fail ran most own
  peak' cnt' fail' ran',
  afn_pre_x segs B ARx STK ly S Hp W regs mem md ch -> In (g, Z.of_nat n) prh_pst ->
  aregs_preserved regs regs' ->
  (forall x : word, ~ (g <= bv_unsigned x < g + Z.of_nat n) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  (forall x : word, w_H W x = true -> mem' x = mem x) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  prh_glob W mem' (Ledger.lsum Lam) peak' cnt' fail' ran' most own ->
  fpostm B ARx SK STK [] regs ly S Hp W mem md
    (fun ly' S' Hp' W' regs'' mem'' md' => (room_live_cf S -> room_live_cf S') /\ Hp' = Hp /\
       S' = S /\ ablocks B ly' S' = ablocks B ly S /\
       prh_ledger B ly' S' Hp' W' mem'' Lam peak' cnt' fail' ran' most own)
    W (mkCfg (YK11.mkst regs' (YK11.getr regs 1) mem' (YK11.seg_rom segs)) (with_vm_backing (m_vm_lazy md) X md)).
Proof.
intros STK ly S Hp W regs mem md ch regs' mem' X g n Lam peak cnt fail ran most own peak' cnt' fail' ran'
  HPRE Hc Hpr Hfr Hgr Hhid HL0 HG'.
pose proof HPRE as (HAR & _).
pose proof asan_consts as (C1 & _).
unfold fpostm, fQmn, fpost, apost_base_x.
exists ly, S, Hp, regs', mem', (with_vm_backing (m_vm_lazy md) X md), 0.
split; [reflexivity|].
split.
{ eapply (ajournal_x_pst_write segs B prh_pst ARx LAWS pa_segs_low PST_ok);
    [exact (ajournal_x_init (SK := SK) segs B prh_pst ARx STK [] ly S Hp W regs mem md ch HPRE)
    | | exact Hgr | exact Hhid | apply same_but_materialized_wvb_any].
  intros x Hx. apply Hfr. intros Hin. apply Hx. exact (pas_cell_pst g (Z.of_nat n) _ Hc Hin). }
split; [exact Hpr|].
cbv beta. split.
{ split; [exact (fun h => h)|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  apply (prh_ledger_frame B ly S Hp W mem ly S Hp W mem' Lam peak cnt fail ran peak' cnt' fail' ran' most own HL0 HG').
  - intros a k i Hin Hi.
    destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HL0 Hin) as (Hk & Hbl & _).
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hbl) as (_ & H4096 & Hceil & _).
    assert (Hreq : 0 < req_size (k + cf_head)) by (apply prh_req_size_pos; pose proof (@cf_head_nonneg cp); lia).
    apply (prh_mbyte_of_mrestrict (fun z => g <= z < g + Z.of_nat n)); [exact Hfr | lia |].
    exact (pas_head_off ly S Hp W mem md Lam peak cnt fail ran most own g n a k i HAR HL0 Hc Hin Hi).
  - intros a k _ Hb. exact Hb.
  - apply Permutation_refl. }
(* memnorm is kept: the only change is inside the written cell, which is below TASK_SIZE and writable *)
{ intros HMN.
  apply (pas_memnorm_frame segs mem mem' g (g + Z.of_nat n) HMN).
  - intros x Hx. destruct (w_H W x) eqn:Ew; [exact (Hhid x Ew)|].
    pose proof (Hfr x Hx) as E. unfold mrestrict in E. rewrite Ew in E. exact E.
  - pose proof (proj1 (forallb_forall _ _) PST_top _ Hc) as T. cbn [fst snd] in T. apply Z.leb_le in T. exact T.
  - intros x b Hx _. pose proof (PST_rw _ (pas_cell_pst g (Z.of_nat n) _ Hc Hx)) as R.
    unfold YAkMemnorm.ro_addr.
    destruct (find_segment segs (bv_unsigned x) 1) as [seg|] eqn:Ef;
      [rewrite ?Ef in R; rewrite R; reflexivity | reflexivity]. }
Qed.

Lemma pas_in_live : In (pi_g_live, Z.of_nat pi_gz_live) prh_pst.
Proof. unfold prh_pst. cbn [In]. left. reflexivity. Qed.
Lemma pas_in_peak : In (pi_g_peak, Z.of_nat pi_gz_peak) prh_pst.
Proof. unfold prh_pst. cbn [In]. right. left. reflexivity. Qed.
Lemma pas_in_count : In (pi_g_count, Z.of_nat pi_gz_count) prh_pst.
Proof. unfold prh_pst. cbn [In]. right. right. left. reflexivity. Qed.
Lemma pas_in_fail : In (pi_g_fail, Z.of_nat pi_gz_fail) prh_pst.
Proof. unfold prh_pst. cbn [In]. right. right. right. left. reflexivity. Qed.
Lemma pas_in_ran : In (pi_g_ran_out, Z.of_nat pi_gz_ran_out) prh_pst.
Proof. unfold prh_pst. cbn [In]. right. right. right. right. left. reflexivity. Qed.
Lemma pas_in_most : In (pi_g_most, Z.of_nat pi_gz_most) prh_pst.
Proof. unfold prh_pst. cbn [In]. right. right. right. right. right. left. reflexivity. Qed.
Lemma pas_in_own : In (pi_g_own_ran_out, Z.of_nat pi_gz_own_ran_out) prh_pst.
Proof. unfold prh_pst. cbn [In]. right. right. right. right. right. right. left. reflexivity. Qed.

(* ---- the five cores ---- *)
Lemma pas_live_core : pas_rd_run segs (pa_sigma AS_fuzz_alloc_live) pi_g_live pi_gz_live ->
  tfuzz_alloc_live_specX B ARx SK.
Proof.
intros RUN. unfold tfuzz_alloc_live_specX.
intros ly S Hp W regs mem md ch Lam peak cnt fail ran most own [HPRE _] HL0.
pose proof HPRE as (_ & Hra & _). pose proof HL0 as ((GL & _ & _ & _ & _ & _ & _ & Rlp & Rpk & _) & _).
apply (RUN W regs mem md (Ledger.lsum Lam) _ Hra GL ltac:(lia)).
intros regs' X H10 Hpr.
exact (pas_rd_post _ ly S Hp W regs mem md ch regs' X Lam peak cnt fail ran most own _ HPRE Hpr H10 HL0).
Qed.

Lemma pas_peak_core : pas_rd_run segs (pa_sigma AS_fuzz_alloc_peak) pi_g_peak pi_gz_peak ->
  tfuzz_alloc_peak_specX B ARx SK.
Proof.
intros RUN. unfold tfuzz_alloc_peak_specX.
intros ly S Hp W regs mem md ch Lam peak cnt fail ran most own [HPRE _] HL0.
pose proof HPRE as (_ & Hra & _). pose proof HL0 as ((_ & GP & _ & _ & _ & _ & _ & Rlp & Rpk & _) & _).
pose proof (prh_lsum_nonneg Lam (prh_ledger_sizes B ly S Hp W mem Lam peak cnt fail ran most own HL0)) as Hl0.
apply (RUN W regs mem md peak _ Hra GP ltac:(lia)).
intros regs' X H10 Hpr.
exact (pas_rd_post _ ly S Hp W regs mem md ch regs' X Lam peak cnt fail ran most own _ HPRE Hpr H10 HL0).
Qed.

Lemma pas_count_core : pas_rd_run segs (pa_sigma AS_fuzz_alloc_count) pi_g_count pi_gz_count ->
  tfuzz_alloc_count_specX B ARx SK.
Proof.
intros RUN. unfold tfuzz_alloc_count_specX.
intros ly S Hp W regs mem md ch Lam peak cnt fail ran most own [HPRE _] HL0.
pose proof HPRE as (_ & Hra & _). pose proof HL0 as ((_ & _ & GC & _ & _ & _ & _ & _ & _ & Rc & _) & _).
apply (RUN W regs mem md cnt _ Hra GC Rc).
intros regs' X H10 Hpr.
exact (pas_rd_post _ ly S Hp W regs mem md ch regs' X Lam peak cnt fail ran most own _ HPRE Hpr H10 HL0).
Qed.

Lemma pas_peak_reset_core :
  pas_wr_run segs (pa_sigma AS_fuzz_alloc_peak_reset) pi_g_live pi_gz_live pi_g_peak pi_gz_peak (fun v _ => v) ->
  tfuzz_alloc_peak_reset_specX B ARx SK.
Proof.
intros RUN. unfold tfuzz_alloc_peak_reset_specX.
intros ly S Hp W regs mem md ch Lam peak cnt fail ran most own [HPRE _] HL0.
pose proof HPRE as (_ & Hra & _).
pose proof HL0 as ((GL & GP & GC & GF & GR & GM & GO & Rlp & Rpk & Rc & Rf & Rr) & _).
destruct (pas_sep7 _ _ _ _ _ _ _ PST_sep) as (Dlp & Dlc & Dlf & Dlr & Dlm & Dlo & Dpc & Dpf & Dpr & Dpm & Dpo &
  Dcf & Dcr & Dcm & Dco & Dfr & Dfm & Dfo & Drm & Dro & Dmo).
pose proof (bv_unsigned_in_range 64 (getr regs 10)) as R10. change (bv_modulus 64) with (2 ^ 64) in R10.
apply (RUN W regs mem md (Ledger.lsum Lam) (bv_unsigned (getr regs 10)) _ Hra
  ltac:(unfold w64; symmetry; apply Z_to_bv_bv_unsigned) R10 GL ltac:(lia)).
intros regs' mem' X Hpr Hfr Hgr Hhid GP'.
apply (pas_wr_post _ ly S Hp W regs mem md ch regs' mem' X _ _ Lam peak cnt fail ran most own
  (Ledger.lsum Lam) cnt fail ran HPRE pas_in_peak Hpr Hfr Hgr Hhid HL0).
unfold prh_glob.
split; [exact (pas_glob_keep W mem mem' _ _ _ _ _ pas_in_peak pas_in_live (prh_zdisjoint_sym _ _ Dlp) Hfr GL)|].
split; [exact GP'|].
split; [exact (pas_glob_keep W mem mem' _ _ _ _ _ pas_in_peak pas_in_count Dpc Hfr GC)|].
split; [exact (pas_glob_keep W mem mem' _ _ _ _ _ pas_in_peak pas_in_fail Dpf Hfr GF)|].
split; [exact (pas_glob_keep W mem mem' _ _ _ _ _ pas_in_peak pas_in_ran Dpr Hfr GR)|].
split; [destruct GM as [GM1 GM2]; split;
  [exact (pas_glob_keep W mem mem' _ _ _ _ _ pas_in_peak pas_in_most Dpm Hfr GM1) | exact GM2]|].
split; [destruct GO as [GO1 GO2]; split;
  [exact (pas_glob_keep W mem mem' _ _ _ _ _ pas_in_peak pas_in_own Dpo Hfr GO1) | exact GO2]|].
repeat split; lia.
Qed.

Lemma pas_fail_core :
  pas_wr_run segs (pa_sigma AS_fuzz_alloc_fail) pi_g_count pi_gz_count pi_g_fail pi_gz_fail
    (fun c k => if k <? SIZE_MAXZ - c then c + k else SIZE_MAXZ) ->
  tfuzz_alloc_fail_specX B ARx SK.
Proof.
intros RUN. unfold tfuzz_alloc_fail_specX.
intros ly S Hp W regs mem md ch Lam peak cnt fail ran k most own [HPRE _] HL0 H10 Hk.
pose proof HPRE as (_ & Hra & _).
pose proof HL0 as ((GL & GP & GC & GF & GR & GM & GO & Rlp & Rpk & Rc & Rf & Rr) & _).
destruct (pas_sep7 _ _ _ _ _ _ _ PST_sep) as (Dlp & Dlc & Dlf & Dlr & Dlm & Dlo & Dpc & Dpf & Dpr & Dpm & Dpo &
  Dcf & Dcr & Dcm & Dco & Dfr & Dfm & Dfo & Drm & Dro & Dmo).
apply (RUN W regs mem md cnt k _ Hra H10 Hk GC Rc).
intros regs' mem' X Hpr Hfr Hgr Hhid GF'.
apply (pas_wr_post _ ly S Hp W regs mem md ch regs' mem' X _ _ Lam peak cnt fail ran most own peak cnt _ ran
  HPRE pas_in_fail Hpr Hfr Hgr Hhid HL0).
unfold prh_glob.
split; [exact (pas_glob_keep W mem mem' _ _ _ _ _ pas_in_fail pas_in_live (prh_zdisjoint_sym _ _ Dlf) Hfr GL)|].
split; [exact (pas_glob_keep W mem mem' _ _ _ _ _ pas_in_fail pas_in_peak (prh_zdisjoint_sym _ _ Dpf) Hfr GP)|].
split; [exact (pas_glob_keep W mem mem' _ _ _ _ _ pas_in_fail pas_in_count (prh_zdisjoint_sym _ _ Dcf) Hfr GC)|].
split; [exact GF'|].
split; [exact (pas_glob_keep W mem mem' _ _ _ _ _ pas_in_fail pas_in_ran Dfr Hfr GR)|].
split; [destruct GM as [GM1 GM2]; split;
  [exact (pas_glob_keep W mem mem' _ _ _ _ _ pas_in_fail pas_in_most Dfm Hfr GM1) | exact GM2]|].
split; [destruct GO as [GO1 GO2]; split;
  [exact (pas_glob_keep W mem mem' _ _ _ _ _ pas_in_fail pas_in_own Dfo Hfr GO1) | exact GO2]|].
destruct (Z.ltb_spec k (SIZE_MAXZ - cnt)); unfold SIZE_MAXZ in *; repeat split; lia.
Qed.

End c.

(* ==== 4. image A' (asan, #102: PI_prog_A / prh_img_A on the #102 pins): the byte runs, then the five texts ==== *)
(* image facts of prh_img_A's seven statics, by computation on the concrete segments (S1ImgA.v:26-55's checkers,
   copied, not imported) *)
Definition pas_wv_b (segs : list Segment) (a : Z) : bool :=
  match wview segs (fun _ => None) (Z_to_bv 64 a) with Some _ => true | None => false end.
Definition pas_in_img_b (segs : list Segment) (a : Z) : bool :=
  existsb (fun s => (Z.of_N (seg_base s) <=? a) && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s))) segs.
Definition pas_pst_allb (f : Z -> bool) (P : list (Z * Z)) : bool :=
  forallb (fun r => zallb f (fst r) (Z.to_nat (snd r))) P.
Lemma pas_pst_allb_sound : forall f P a, pas_pst_allb f P = true -> Exists (in_zr a) P -> f a = true.
Proof.
intros f P a H Ha. apply Exists_exists in Ha as (r & Hr & Ha). unfold pas_pst_allb in H.
rewrite forallb_forall in H. specialize (H r Hr). unfold in_zr in Ha.
apply (zallb_sound f (Z.to_nat (snd r)) (fst r) a H). rewrite Z2Nat.id by lia. lia.
Qed.
Lemma pas_writable_of_wv_b : forall segs (m : word -> option byte) a, pas_wv_b segs a = true -> writable_at segs m a.
Proof.
intros segs m a H. unfold writable_at. apply (seg_win_wview segs a 1 m a); [| lia | lia].
change (pas_wv_b segs a && true = true). rewrite H. reflexivity.
Qed.
Lemma pas_in_img_b_sound : forall segs a, pas_in_img_b segs a = true -> in_img segs a.
Proof.
intros segs a H. apply existsb_exists in H as (s & Hs & H). apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists s. split; [exact Hs | lia].
Qed.
Lemma pas_pst_wv_A : pas_pst_allb (pas_wv_b rsegs) (@prh_pst prh_img_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pas_pst_img_b_A : pas_pst_allb (pas_in_img_b rsegs) (@prh_pst prh_img_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pas_pst_writable_A : forall (m : word -> option byte) a,
  Exists (in_zr a) (@prh_pst prh_img_A) -> writable_at rsegs m a.
Proof. intros m a Ha. apply pas_writable_of_wv_b. exact (pas_pst_allb_sound _ _ a pas_pst_wv_A Ha). Qed.
Lemma pas_pst_img_A : forall a, Exists (in_zr a) (@prh_pst prh_img_A) -> in_img rsegs a.
Proof. intros a Ha. apply pas_in_img_b_sound. exact (pas_pst_allb_sound _ _ a pas_pst_img_b_A Ha). Qed.
Lemma pas_pst_sep_A : YG0f.pairwise zdisjoint (@prh_pst prh_img_A).
Proof.
unfold prh_pst. cbn [YG0f.pairwise].
repeat match goal with
| |- _ /\ _ => split
| |- True => exact I
| |- Forall _ [] => apply Forall_nil
| |- Forall _ (_ :: _) => apply Forall_cons; [unfold zdisjoint; cbn; lia|]
end.
Qed.
Lemma pas_pst_al_A : Forall (fun r => fst r mod 8 = 0 /\ 0 <= snd r <= 8) (@prh_pst prh_img_A).
Proof.
unfold prh_pst.
repeat match goal with
| |- Forall _ [] => apply Forall_nil
| |- Forall _ (_ :: _) => apply Forall_cons; [cbn; split; [reflexivity | lia]|]
end.
Qed.
(* the m-form post's two image facts at image A', by computation over the seven statics *)
Definition pas_rw_b (segs : list Segment) (a : Z) : bool :=
  match find_segment segs a 1 with Some seg => seg_writable seg | None => true end.
Lemma pas_pst_rw_b_A : pas_pst_allb (pas_rw_b rsegs) (@prh_pst prh_img_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pas_pst_rw_A : forall a, Exists (in_zr a) (@prh_pst prh_img_A) ->
  match find_segment rsegs a 1 with Some seg => seg_writable seg = true | None => True end.
Proof.
intros a Ha. pose proof (pas_pst_allb_sound _ _ a pas_pst_rw_b_A Ha) as H. unfold pas_rw_b in H.
destruct (find_segment rsegs a 1); [exact H | exact I].
Qed.
Lemma pas_pst_top_A : forallb (fun r => fst r + snd r <=? TASK_SIZE) (@prh_pst prh_img_A) = true.
Proof. vm_compute. reflexivity. Qed.

(* the tables: the function's own words read from the image (LENGTH 3 / 5 / 9: the listing's word counts) *)
Definition tbl_lv : ctable := Eval vm_compute in build_table rsegs (A_prog_sigma AS_fuzz_alloc_live) 3 TEmpty.
Lemma tbl_lv_ok : table_ok rsegs tbl_lv.
Proof.
assert (E : tbl_lv = build_table rsegs (A_prog_sigma AS_fuzz_alloc_live) 3 TEmpty) by (vm_cast_no_check (eq_refl tbl_lv)).
rewrite E. apply build_table_ok0. cbv. discriminate.
Qed.
Definition tbl_pk : ctable := Eval vm_compute in build_table rsegs (A_prog_sigma AS_fuzz_alloc_peak) 3 TEmpty.
Lemma tbl_pk_ok : table_ok rsegs tbl_pk.
Proof.
assert (E : tbl_pk = build_table rsegs (A_prog_sigma AS_fuzz_alloc_peak) 3 TEmpty) by (vm_cast_no_check (eq_refl tbl_pk)).
rewrite E. apply build_table_ok0. cbv. discriminate.
Qed.
Definition tbl_ct : ctable := Eval vm_compute in build_table rsegs (A_prog_sigma AS_fuzz_alloc_count) 3 TEmpty.
Lemma tbl_ct_ok : table_ok rsegs tbl_ct.
Proof.
assert (E : tbl_ct = build_table rsegs (A_prog_sigma AS_fuzz_alloc_count) 3 TEmpty) by (vm_cast_no_check (eq_refl tbl_ct)).
rewrite E. apply build_table_ok0. cbv. discriminate.
Qed.
Definition tbl_pr : ctable := Eval vm_compute in build_table rsegs (A_prog_sigma AS_fuzz_alloc_peak_reset) 5 TEmpty.
Lemma tbl_pr_ok : table_ok rsegs tbl_pr.
Proof.
assert (E : tbl_pr = build_table rsegs (A_prog_sigma AS_fuzz_alloc_peak_reset) 5 TEmpty) by (vm_cast_no_check (eq_refl tbl_pr)).
rewrite E. apply build_table_ok0. cbv. discriminate.
Qed.
Definition tbl_fl : ctable := Eval vm_compute in build_table rsegs (A_prog_sigma AS_fuzz_alloc_fail) 9 TEmpty.
Lemma tbl_fl_ok : table_ok rsegs tbl_fl.
Proof.
assert (E : tbl_fl = build_table rsegs (A_prog_sigma AS_fuzz_alloc_fail) 9 TEmpty) by (vm_cast_no_check (eq_refl tbl_fl)).
rewrite E. apply build_table_ok0. cbv. discriminate.
Qed.

(* the symbolic entry states: atom 32 is the static read; a write cell for the static written *)
Definition pas_rcell (g : Z) (n : nat) : YP09.region := pw_rcell g (Z.of_nat n) 32.
Definition pas_wcell (g : Z) (n : nat) : YP09.region := pw_wcell g (Z.of_nat n).
Definition ss_rd (pc g : Z) (n : nat) : sstate := mkSS pc sr_atoms [pas_rcell g n] None (mkFacts [] [] []).
Definition ss_wr (pc gs : Z) (ns : nat) (gd : Z) (nd : nat) : sstate :=
  mkSS pc sr_atoms [pas_rcell gs ns; pas_wcell gd nd] None (mkFacts [] [] []).

(* the saturating sum the bytes compute (alloc.c :149-152; the `add` / `sltu` / `neg` / `or` of the listing): with
   s = (k + c) mod 2 ^ 64 and the carry (s <u c), s | -carry is the text's `k < SIZE_MAX - c ? c + k : SIZE_MAX`: no wrap
   below SIZE_MAX, the boundary c + k = SIZE_MAX (no wrap, both give SIZE_MAX), and the wrap (all ones) *)
Lemma pas_lor_ones : forall s, 0 <= s < 2 ^ 64 -> Z.lor (2 ^ 64 - 1) s = 2 ^ 64 - 1.
Proof.
intros s Hs. replace (2 ^ 64 - 1) with (Z.ones 64) by reflexivity.
apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
destruct (Z_lt_le_dec i 64) as [Hl|Hg].
- rewrite Z.ones_spec_low by lia. reflexivity.
- rewrite Z.ones_spec_high by lia. cbn [orb]. rewrite <- (Z.mod_small s (2 ^ 64)) by lia.
  rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma pas_sat : forall c k, 0 <= c < 2 ^ 64 -> 0 <= k < 2 ^ 64 ->
  zcanon (Z.lor (zcanon (zcanon 0 - zcanon (if zcanon (k + c) <? c then 1 else 0))) (zcanon (k + c))) =
  (if k <? SIZE_MAXZ - c then c + k else SIZE_MAXZ).
Proof.
intros c k Hc Hk. unfold zcanon, M64, SIZE_MAXZ.
destruct (Z_lt_le_dec (k + c) (2 ^ 64)) as [Hn|Hw].
- rewrite (Z.mod_small (k + c)) by lia.
  rewrite (proj2 (Z.ltb_ge (k + c) c)) by lia.
  replace ((0 mod 2 ^ 64 - (if false then 1 else 0) mod 2 ^ 64) mod 2 ^ 64) with 0 by reflexivity.
  rewrite Z.lor_0_l. rewrite Z.mod_small by lia.
  destruct (Z.ltb_spec k (2 ^ 64 - 1 - c)); lia.
- assert (Es : (k + c) mod 2 ^ 64 = k + c - 2 ^ 64).
  { replace (k + c) with ((k + c - 2 ^ 64) + 1 * 2 ^ 64) at 1 by lia. rewrite Z.mod_add by lia.
    apply Z.mod_small. lia. }
  rewrite Es. rewrite (proj2 (Z.ltb_lt (k + c - 2 ^ 64) c)) by lia.
  replace ((0 mod 2 ^ 64 - (if true then 1 else 0) mod 2 ^ 64) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
  rewrite pas_lor_ones by lia. rewrite (proj2 (Z.ltb_ge k (2 ^ 64 - 1 - c))) by lia. reflexivity.
Qed.

(* ---- image A's runs ---- *)
Section A. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* the entry states (st_ok) of a reader and of a writer over the concrete segments *)
Lemma pas_rd_entry : forall regs mem (H : word -> bool) pc g n v,
  regions_wf [pas_rcell g n] = true ->
  val_mem rsegs (mrestrict H mem) g n v -> 0 <= v < 2 ^ (8 * Z.of_nat n) -> (0 < n <= 8)%nat -> 0 <= g ->
  g + Z.of_nat n <= 2 ^ 64 ->
  st_ok rsegs (Ereg regs [w64 v]) (ss_rd pc g n) (restrict H (mkst regs (Z_to_bv 64 pc) mem (seg_rom rsegs))).
Proof.
intros regs mem H pc g n v Hwf GV Hv Hn Hg Hgn. rewrite restrict_mkst_fx. unfold ss_rd. apply entry_st_ok.
- exact Hwf.
- apply Forall_cons; [|apply Forall_nil]. unfold pas_rcell.
  apply (region_ok_pw_rcell _ _ g (Z.of_nat n) 32 v); [rewrite Nat2Z.id; exact GV | exact (ew_Ereg_extra regs [w64 v] 0)
    | exact Hv | lia | lia | lia].
- cbn. split; exact I.
- exact I.
Qed.
Lemma pas_wr_entry : forall regs mem (H : word -> bool) pc gs ns gd nd v,
  regions_wf [pas_rcell gs ns; pas_wcell gd nd] = true ->
  (gs + Z.of_nat ns <= gd \/ gd + Z.of_nat nd <= gs) ->
  val_mem rsegs (mrestrict H mem) gs ns v -> 0 <= v < 2 ^ (8 * Z.of_nat ns) -> (0 < ns <= 8)%nat -> 0 <= gs ->
  gs + Z.of_nat ns <= 2 ^ 64 ->
  (forall x, gd <= x < gd + Z.of_nat nd -> writable_at rsegs (mrestrict H mem) x) -> 0 <= gd ->
  gd + Z.of_nat nd <= 2 ^ 64 ->
  st_ok rsegs (Ereg regs [w64 v]) (ss_wr pc gs ns gd nd) (restrict H (mkst regs (Z_to_bv 64 pc) mem (seg_rom rsegs))).
Proof.
intros regs mem H pc gs ns gd nd v Hwf Hd GV Hv Hn Hg Hgn Hw Hd0 Hd1. rewrite restrict_mkst_fx. unfold ss_wr.
apply entry_st_ok.
- exact Hwf.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold pas_rcell.
    apply (region_ok_pw_rcell _ _ gs (Z.of_nat ns) 32 v); [rewrite Nat2Z.id; exact GV | exact (ew_Ereg_extra regs [w64 v] 0)
      | exact Hv | lia | lia | lia].
  + unfold pas_wcell. apply region_ok_pw_wcell; [exact Hw | lia | lia | lia].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, pas_rcell, pas_wcell, pw_rcell, pw_wcell.
  cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi]. split; [split; [lia | exact I] | split; exact I].
- exact I.
Qed.

(* the runs *)
#[local] Abbreviation PA := PI_prog_A.
#[local] Abbreviation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Abbreviation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Abbreviation PIA := prh_img_A.

(* the end of a reader's run: back at ra, a0 = atom 32, memory as it was *)
Ltac pas_rd_ret tbl tblok Hwx Hra HQ HE v :=
  eapply (SRr_ret_at SEGS tbl tblok Hwx _ _); [eassumption | reflexivity | vm_compute; reflexivity |];
  let mat2 := fresh "mat" in intros mat2; rewrite wvb_collapse;
  lazymatch goal with HS : st_ok _ ?E ?ssx (restrict _ ?msx), HF : frame_of _ (ss_mem ?ss0) _ (ms_mem ?msx) |- _ =>
    let Hm := fresh "Hm" in let R1 := fresh "R1" in let R10 := fresh "R10" in
    let E1 := fresh "E1" in let E32 := fresh "E32" in
    assert (Hm : ms_mem msx = _) by exact (frame_of_read_only E (ss_mem ss0) _ _ eq_refl HF);
    rreg HS (1%bv : bv 5) R1; rreg HS (10%bv : bv 5) R10;
    assert (E1 : ew E 1 = getr _ 1) by (rewrite HE; exact (ew_Ereg_nat _ [w64 v] 1 1%bv eq_refl));
    assert (E32 : ew E 32 = w64 v) by (rewrite HE; exact (ew_Ereg_extra _ [w64 v] 0));
    rewrite R1, E1, Hra, Hm;
    apply HQ; [rewrite R10, E32; reflexivity
              | eapply aregs_preserved_of_st_ok; [exact HS | rewrite HE; apply env_agree_refl | vm_compute; reflexivity]]
  end.

Lemma pas_live_run_A : pas_rd_run SEGS (SIGMA AS_fuzz_alloc_live) (@pi_g_live PIA) (@pi_gz_live PIA).
Proof.
intros W regs mem md v Q Hra GV Hv HQ. unfold YK0s.ret_ok in Hra.
pose proof (@pa_wx _ _ PA) as Hwx.
assert (HS : st_ok SEGS (Ereg regs [w64 v]) (ss_rd (A_prog_sigma AS_fuzz_alloc_live) (@pi_g_live PIA) (@pi_gz_live PIA))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (A_prog_sigma AS_fuzz_alloc_live)) mem (seg_rom SEGS))))
  by (apply pas_rd_entry; [vm_compute; reflexivity | exact GV | cbn; lia | cbn; lia | cbn; lia | cbn; lia]).
unfold cfg_at. change (w64 (SIGMA AS_fuzz_alloc_live)) with (Z_to_bv 64 (A_prog_sigma AS_fuzz_alloc_live)).
remember (Ereg regs [w64 v]) as E eqn:HE.
srr_run_with tbl_lv_ok HS.
pas_rd_ret tbl_lv tbl_lv_ok Hwx Hra HQ HE v.
Qed.

Lemma pas_peak_run_A : pas_rd_run SEGS (SIGMA AS_fuzz_alloc_peak) (@pi_g_peak PIA) (@pi_gz_peak PIA).
Proof.
intros W regs mem md v Q Hra GV Hv HQ. unfold YK0s.ret_ok in Hra.
pose proof (@pa_wx _ _ PA) as Hwx.
assert (HS : st_ok SEGS (Ereg regs [w64 v]) (ss_rd (A_prog_sigma AS_fuzz_alloc_peak) (@pi_g_peak PIA) (@pi_gz_peak PIA))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (A_prog_sigma AS_fuzz_alloc_peak)) mem (seg_rom SEGS))))
  by (apply pas_rd_entry; [vm_compute; reflexivity | exact GV | cbn; lia | cbn; lia | cbn; lia | cbn; lia]).
unfold cfg_at. change (w64 (SIGMA AS_fuzz_alloc_peak)) with (Z_to_bv 64 (A_prog_sigma AS_fuzz_alloc_peak)).
remember (Ereg regs [w64 v]) as E eqn:HE.
srr_run_with tbl_pk_ok HS.
pas_rd_ret tbl_pk tbl_pk_ok Hwx Hra HQ HE v.
Qed.

Lemma pas_count_run_A : pas_rd_run SEGS (SIGMA AS_fuzz_alloc_count) (@pi_g_count PIA) (@pi_gz_count PIA).
Proof.
intros W regs mem md v Q Hra GV Hv HQ. unfold YK0s.ret_ok in Hra.
pose proof (@pa_wx _ _ PA) as Hwx.
assert (HS : st_ok SEGS (Ereg regs [w64 v]) (ss_rd (A_prog_sigma AS_fuzz_alloc_count) (@pi_g_count PIA) (@pi_gz_count PIA))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (A_prog_sigma AS_fuzz_alloc_count)) mem (seg_rom SEGS))))
  by (apply pas_rd_entry; [vm_compute; reflexivity | exact GV | cbn; lia | cbn; lia | cbn; lia | cbn; lia]).
unfold cfg_at. change (w64 (SIGMA AS_fuzz_alloc_count)) with (Z_to_bv 64 (A_prog_sigma AS_fuzz_alloc_count)).
remember (Ereg regs [w64 v]) as E eqn:HE.
srr_run_with tbl_ct_ok HS.
pas_rd_ret tbl_ct tbl_ct_ok Hwx Hra HQ HE v.
Qed.

(* a writer's run up to its ret, by pas_run_hid *)
Ltac pas_wr_go tbl tblok Hwx HS :=
  lazymatch type of HS with st_ok ?segs ?E0 ?ss (restrict (w_H ?W0) ?ms) =>
    let r := eval vm_compute in (sym_runN segs tbl FUEL ss) in
    lazymatch r with (?ss', ?st) =>
      let Hrun := fresh "Hrun" in
      assert (Hrun : sym_runN segs tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
      apply (pas_run_hid segs tbl tblok Hwx W0 FUEL E0 ss ss' st ms _ _ HS Hrun I)
    end
  end.
(* the frame of a writer's run: only the write cell's bytes may change *)
Ltac pas_wr_frame HFr :=
  let x := fresh "x" in let Hx := fresh "Hx" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros x Hx; apply HFr; intros (r & Hin & Hr); apply Hx;
  cbn [ss_mem ss_wr In] in Hin; destruct Hin as [<-|[<-|[]]];
  unfold pas_rcell, pas_wcell, pw_rcell, pw_wcell in Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia.

Lemma pas_peak_reset_run_A :
  pas_wr_run SEGS (SIGMA AS_fuzz_alloc_peak_reset) (@pi_g_live PIA) (@pi_gz_live PIA) (@pi_g_peak PIA) (@pi_gz_peak PIA)
    (fun v _ => v).
Proof.
intros W regs mem md v a0 Q Hra _ _ GV Hv HQ. unfold YK0s.ret_ok in Hra.
pose proof (@pa_wx _ _ PA) as Hwx.
assert (HS : st_ok SEGS (Ereg regs [w64 v])
  (ss_wr (A_prog_sigma AS_fuzz_alloc_peak_reset) (@pi_g_live PIA) (@pi_gz_live PIA) (@pi_g_peak PIA) (@pi_gz_peak PIA))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (A_prog_sigma AS_fuzz_alloc_peak_reset)) mem (seg_rom SEGS)))).
{ apply pas_wr_entry; [vm_compute; reflexivity | cbn; lia | exact GV | cbn; lia | cbn; lia | cbn; lia | cbn; lia
    | | cbn; lia | cbn; lia].
  intros x Hx. apply pas_pst_writable_A. exact (pas_cell_pst (PI := PIA) _ _ x pas_in_peak Hx). }
unfold cfg_at. change (w64 (SIGMA AS_fuzz_alloc_peak_reset)) with (Z_to_bv 64 (A_prog_sigma AS_fuzz_alloc_peak_reset)).
remember (Ereg regs [w64 v]) as E eqn:HE.
pas_wr_go tbl_pr tbl_pr_ok Hwx HS.
intros ms' mat' HS' HFr Hgr Hhid. clear HS.
eapply (SRr_ret_at SEGS tbl_pr tbl_pr_ok Hwx W E); [exact HS' | reflexivity | vm_compute; reflexivity |].
intros mat2. rewrite wvb_collapse.
rreg HS' (1%bv : bv 5) R1.
assert (E1 : ew E 1 = getr regs 1) by (rewrite HE; exact (ew_Ereg_nat regs [w64 v] 1 1%bv eq_refl)).
assert (E32 : ew E 32 = w64 v) by (rewrite HE; exact (ew_Ereg_extra regs [w64 v] 0)).
rewrite R1, E1, Hra.
destruct (st_ok_mem_ok SEGS E _ _ HS') as (_ & HRS & _). cbn [ms_mem restrict] in HRS.
apply Forall_inv_tail in HRS. apply Forall_inv in HRS.
unfold region_ok in HRS. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HRS.
destruct HRS as (_ & _ & _ & HCk). apply Forall_inv in HCk.
assert (Hden : sv_denot E (SOff 32 0) = Z_to_bv 64 v).
{ cbn [sv_denot]. rewrite E32. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia. }
pose proof (val_of_chunk_ok SEGS E _ 0 _ 8 (SOff 32 0) v HCk Hden ltac:(cbn; lia) ltac:(cbn; lia)) as V.
apply HQ.
- eapply aregs_preserved_of_st_ok; [exact HS' | rewrite HE; apply env_agree_refl | vm_compute; reflexivity].
- pas_wr_frame HFr.
- exact Hgr.
- exact Hhid.
- exact V.
Qed.

Lemma pas_fail_run_A :
  pas_wr_run SEGS (SIGMA AS_fuzz_alloc_fail) (@pi_g_count PIA) (@pi_gz_count PIA) (@pi_g_fail PIA) (@pi_gz_fail PIA)
    (fun c k => if k <? SIZE_MAXZ - c then c + k else SIZE_MAXZ).
Proof.
intros W regs mem md v k Q Hra H10 Hk GV Hv HQ. unfold YK0s.ret_ok in Hra.
pose proof (@pa_wx _ _ PA) as Hwx.
assert (HS : st_ok SEGS (Ereg regs [w64 v])
  (ss_wr (A_prog_sigma AS_fuzz_alloc_fail) (@pi_g_count PIA) (@pi_gz_count PIA) (@pi_g_fail PIA) (@pi_gz_fail PIA))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (A_prog_sigma AS_fuzz_alloc_fail)) mem (seg_rom SEGS)))).
{ apply pas_wr_entry; [vm_compute; reflexivity | cbn; lia | exact GV | cbn; lia | cbn; lia | cbn; lia | cbn; lia
    | | cbn; lia | cbn; lia].
  intros x Hx. apply pas_pst_writable_A. exact (pas_cell_pst (PI := PIA) _ _ x pas_in_fail Hx). }
unfold cfg_at. change (w64 (SIGMA AS_fuzz_alloc_fail)) with (Z_to_bv 64 (A_prog_sigma AS_fuzz_alloc_fail)).
remember (Ereg regs [w64 v]) as E eqn:HE.
pas_wr_go tbl_fl tbl_fl_ok Hwx HS.
intros ms' mat' HS' HFr Hgr Hhid. clear HS.
eapply (SRr_ret_at SEGS tbl_fl tbl_fl_ok Hwx W E); [exact HS' | reflexivity | vm_compute; reflexivity |].
intros mat2. rewrite wvb_collapse.
rreg HS' (1%bv : bv 5) R1.
assert (E1 : ew E 1 = getr regs 1) by (rewrite HE; exact (ew_Ereg_nat regs [w64 v] 1 1%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 k) by (rewrite HE; rewrite (ew_Ereg_nat regs [w64 v] 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 v) by (rewrite HE; exact (ew_Ereg_extra regs [w64 v] 0)).
rewrite R1, E1, Hra.
destruct (st_ok_mem_ok SEGS E _ _ HS') as (_ & HRS & _). cbn [ms_mem restrict] in HRS.
apply Forall_inv_tail in HRS. apply Forall_inv in HRS.
unfold region_ok in HRS. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HRS.
destruct HRS as (_ & _ & _ & HCk). apply Forall_inv in HCk.
set (e := SAlu Instr.ALU_OR (SAlu Instr.ALU_SUB (SLit 0)
    (SAlu Instr.ALU_SLTU (SAlu Instr.ALU_ADD (SOff 10 0) (SOff 32 0)) (SOff 32 0)))
  (SAlu Instr.ALU_ADD (SOff 10 0) (SOff 32 0))) in HCk.
assert (HU : U E e = (if k <? SIZE_MAXZ - v then v + k else SIZE_MAXZ)).
{ subst e. rewrite !U_SAlu, U_SLit, (U_atom E 10 k E10 Hk), (U_atom E 32 v E32 Hv). cbn [zalu_raw].
  exact (pas_sat v k Hv Hk). }
assert (Hden : sv_denot E e = Z_to_bv 64 (if k <? SIZE_MAXZ - v then v + k else SIZE_MAXZ))
  by (rewrite <- HU; unfold U; symmetry; apply Z_to_bv_bv_unsigned).
assert (Hrg : 0 <= (if k <? SIZE_MAXZ - v then v + k else SIZE_MAXZ) < 2 ^ (8 * Z.of_N 8))
  by (destruct (Z.ltb_spec k (SIZE_MAXZ - v)); unfold SIZE_MAXZ in *; cbn; lia).
pose proof (val_of_chunk_ok SEGS E _ 0 _ 8 e _ HCk Hden Hrg ltac:(cbn; lia)) as V.
apply HQ.
- eapply aregs_preserved_of_st_ok; [exact HS' | rewrite HE; apply env_agree_refl | vm_compute; reflexivity].
- pas_wr_frame HFr.
- exact Hgr.
- exact Hhid.
- exact V.
Qed.
End A.

(* ---- the five TEXTS (a Theorem Labs lane, lib/A/PRH_FnAlloc.v:136-190) at image A' (#102): PA := PI_prog_A, PI := prh_img_A,
   preset's CfParams, and FuzzStrdup's allocator relation (ARcf with the error-buffer extents placed). Each is its
   core (section 3) with the byte run of section 4. ---- *)
Section T. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
Context {SK : YI16.sink_head}.
#[local] Abbreviation CP := CfParams_preset.
#[local] Abbreviation PA := PI_prog_A.
#[local] Abbreviation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Abbreviation PIA := prh_img_A.
Variable B : asyms.
#[local] Abbreviation ARc := (fun ly S Hp W mem md => ARcf (cp := CP) SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
(* the allocator's laws at ARcf: h-mani-a8's AR_laws_ok_cf (YG0lawscf.v), and AR_laws_x from them (YGcallcf.v),
   exactly as FuzzStrdup.v:234-235 *)
Let LAWS_cf : AR_laws_cf (cp := CP) SEGS B := AR_laws_ok_cf (cp := CP) SEGS B.
Let LAWS : AR_laws_x SEGS B ARc (@cf_head CP) := AR_laws_x_xs (cp := CP) SEGS B LAWS_cf.
(* PST_ok's B half: the seven statics are not runtime-owned statics of B (its image half is pas_pst_img_A). Its
   instance witness at the real A' record is PwAllocSurfSat.v's PST_unowned_at_TfibB (B := AD2l.TfibB). *)
Hypothesis PST_unowned : forall a, Exists (in_zr a) (@prh_pst PIA) -> ~ Exists (in_zr a) (as_owned_static B).
Let PST_OK : forall a, Exists (in_zr a) (@prh_pst PIA) -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) :=
  fun a H => conj (pas_pst_img_A a H) (PST_unowned a H).

(* GENERIC in the room-live instance: a consumer that is itself generic in RL cites these *)
Theorem fuzz_alloc_live_holds_rl {RL : PrhRoomLive} : tfuzz_alloc_live_specX (cp := CP) (PI := PIA) (PA := PA) B ARc SK.
Proof. exact (pas_live_core B ARc SK _ LAWS pas_live_run_A). Qed.

Theorem fuzz_alloc_peak_holds_rl {RL : PrhRoomLive} : tfuzz_alloc_peak_specX (cp := CP) (PI := PIA) (PA := PA) B ARc SK.
Proof. exact (pas_peak_core B ARc SK _ LAWS pas_peak_run_A). Qed.

Theorem fuzz_alloc_peak_reset_holds_rl {RL : PrhRoomLive} :
  tfuzz_alloc_peak_reset_specX (cp := CP) (PI := PIA) (PA := PA) B ARc SK.
Proof.
exact (pas_peak_reset_core B ARc SK _ LAWS PST_OK pas_pst_sep_A pas_pst_al_A pas_pst_rw_A pas_pst_top_A
  pas_peak_reset_run_A).
Qed.

Theorem fuzz_alloc_count_holds_rl {RL : PrhRoomLive} : tfuzz_alloc_count_specX (cp := CP) (PI := PIA) (PA := PA) B ARc SK.
Proof. exact (pas_count_core B ARc SK _ LAWS pas_count_run_A). Qed.

Theorem fuzz_alloc_fail_holds_rl {RL : PrhRoomLive} : tfuzz_alloc_fail_specX (cp := CP) (PI := PIA) (PA := PA) B ARc SK.
Proof.
exact (pas_fail_core B ARc SK _ LAWS PST_OK pas_pst_sep_A pas_pst_al_A pas_pst_rw_A pas_pst_top_A pas_fail_run_A).
Qed.

(* THE FIVE TOPS, at the kit's room-live instance h-mani-a8's prh_room_live_a8 (PRH_Base.v:218, from YGcfRoomLive's
   proved laws), as S1's FuzzStrdup.v:532 / FuzzFree.v:896 state theirs; the owner's form for the signature *)
Theorem fuzz_alloc_live_holds :
  tfuzz_alloc_live_specX (cp := CP) (PI := PIA) (RL := prh_room_live_a8 (cp := CP)) (PA := PA) B ARc SK.
Proof. exact (fuzz_alloc_live_holds_rl (RL := prh_room_live_a8 (cp := CP))). Qed.

Theorem fuzz_alloc_peak_holds :
  tfuzz_alloc_peak_specX (cp := CP) (PI := PIA) (RL := prh_room_live_a8 (cp := CP)) (PA := PA) B ARc SK.
Proof. exact (fuzz_alloc_peak_holds_rl (RL := prh_room_live_a8 (cp := CP))). Qed.

Theorem fuzz_alloc_peak_reset_holds :
  tfuzz_alloc_peak_reset_specX (cp := CP) (PI := PIA) (RL := prh_room_live_a8 (cp := CP)) (PA := PA) B ARc SK.
Proof. exact (fuzz_alloc_peak_reset_holds_rl (RL := prh_room_live_a8 (cp := CP))). Qed.

Theorem fuzz_alloc_count_holds :
  tfuzz_alloc_count_specX (cp := CP) (PI := PIA) (RL := prh_room_live_a8 (cp := CP)) (PA := PA) B ARc SK.
Proof. exact (fuzz_alloc_count_holds_rl (RL := prh_room_live_a8 (cp := CP))). Qed.

Theorem fuzz_alloc_fail_holds :
  tfuzz_alloc_fail_specX (cp := CP) (PI := PIA) (RL := prh_room_live_a8 (cp := CP)) (PA := PA) B ARc SK.
Proof. exact (fuzz_alloc_fail_holds_rl (RL := prh_room_live_a8 (cp := CP))). Qed.
End T.
