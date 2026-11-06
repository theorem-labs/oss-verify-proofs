(* proves no function (kind: segment lemma): the IMAGE-FREE core of the fuzz_alloc_most walk (fuzz_preset row AL5,
   rewalk preset-F the internal file FREE-PIECES-102.md Part 5), moved out of lib/A/Prog/FuzzAllocMostAp.v so that the B' twin
   lib/B/Prog/FuzzAllocMostBp.v does not Require the A' file (which Requires S1ImgA and so loads image A's PRH_Img /
   PAImg_prog instances; a Theorem Labs lane 21:45Z wrong-image hazard, asked by a Theorem Labs lane 22:33Z). This file Requires no
   lib/A image file (no Img0, Listing_prog, PAImg_prog, PRH_Img, S1ImgA): only the Reusable model files and the
   kit's PRH_Base / CfParamsPreset / PRH_FnCheck / S1Ledger. Statements and proofs are unchanged from
   FuzzAllocMostAp.v at 00261ef4035.
   1. fam_wr_run states the byte run of a writer of its argument as machine behaviour over ANY segments (no journal,
      no ledger), with fam_run_hid, fam_entry and the run / frame tactics fam_wr_go / fam_wr_frame;
   2. fam_sep7: the 21 pairs of prh_pst's seven cells;
   3. fam_most_core, parametric in the image ({PI : PrhImg} {PA : PAImg L}) and in the allocator relation ARx, builds
      the kit's text tfuzz_alloc_most_specX (lib/A/PRH_FnCheck.v:776) from the byte run: the journal by ajournal_x_init then
      ajournal_x_pst_write, the ledger by S1Ledger's prh_ledger_iff / prh_lblocks_kept from PRH_Base's named
      projections (never a positional destruct of prh_ledger); fam_rw_b decides a static's writability per segment
      list (each image file computes it over its own segments).
   NUMERALS: no ADDRESS literal; 8 LENGTH (a word's bytes: the width bound and the alignment of a static, the head
   word); 16 DERIVED (the head's alignment, cf_head_al); 1 LENGTH (find_segment's one-byte window); 64 and 2 ^ 64
   WORD (the machine word's width and modulus); 0 WORD (an absolute region's base). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
(* YGcallcf's import chain loads Reusable/YF0v.v, whose line 16 sets zify's euclidean-division flag to false
   GLOBALLY; the alignment argument below (fam_head_off: a mod 16 = 0, 8-aligned statics) needs lia's mod / div
   support, so this file sets the flag back to the Stdlib default for itself only (PwAllocSurf.v's setting) *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ==== 1. the byte run, as machine behaviour over any segments (no journal, no ledger) ==== *)
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.

(* a writer of its argument: from pc, back at ra with the nd-byte static at gd holding the entry value of a0, every
   other visible byte unchanged, the hidden bytes unchanged, callee-saved kept *)
Definition fam_wr_run (pc gd : Z) (nd : nat) : Prop :=
  forall (W : world segs) regs mem md a0 (Q : world segs -> config -> Prop),
  YK0s.ret_ok (YK11.getr regs 1) -> getr regs 10 = w64 a0 -> 0 <= a0 < 2 ^ 64 ->
  (forall regs' mem' X, aregs_preserved regs regs' ->
     (forall x : word, ~ (gd <= bv_unsigned x < gd + Z.of_nat nd) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
     mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
     (forall x : word, w_H W x = true -> mem' x = mem x) ->
     val_mem segs (mrestrict (w_H W) mem') gd nd a0 ->
     Q W (mkCfg (YK11.mkst regs' (YK11.getr regs 1) mem' (YK11.seg_rom segs)) (with_vm_backing (m_vm_lazy md) X md))) ->
  SRr segs W (cfg_at segs pc regs mem md) Q.

(* the engine's run (YA0o.v SRr_run_gen) with the growth of the visible memory and the hidden bytes exposed, as
   YCbqG.v SRr_chain_AJx_pst reads them off the unrestricted state (PwAllocSurf.v pas_run_hid) *)
Lemma fam_run_hid : forall tbl, table_ok segs tbl -> wx_segs_nowrap segs ->
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

(* the symbolic entry state: one write cell, an absolute region (YP09 base None) with an empty chunk list, at the
   static the function stores *)
Definition fam_wcell (g : Z) (n : nat) : YP09.region := YP09.mkRegion None g (g + Z.of_nat n) g (g + Z.of_nat n) [].
Definition fam_ss (pc gd : Z) (nd : nat) : sstate := mkSS pc sr_atoms [fam_wcell gd nd] None (mkFacts [] [] []).

Lemma fam_entry : forall regs mem (H : word -> bool) pc gd nd,
  regions_wf [fam_wcell gd nd] = true ->
  (forall x, gd <= x < gd + Z.of_nat nd -> writable_at segs (mrestrict H mem) x) -> 0 <= gd ->
  gd + Z.of_nat nd <= 2 ^ 64 ->
  st_ok segs (Ereg regs []) (fam_ss pc gd nd) (restrict H (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs))).
Proof.
intros regs mem H pc gd nd Hwf Hw Hd0 Hd1. rewrite restrict_mkst_fx. unfold fam_ss.
assert (HR : region_ok segs (Ereg regs []) (mrestrict H mem) (fam_wcell gd nd)).
{ unfold region_ok, fam_wcell. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. rewrite Z.add_0_l. apply Hw. lia. }
assert (HF : Forall (region_ok segs (Ereg regs []) (mrestrict H mem)) [fam_wcell gd nd]).
{ apply Forall_cons. - exact HR. - apply Forall_nil. }
assert (HD : pairwise_disjoint (Ereg regs []) [fam_wcell gd nd]) by (cbn [pairwise_disjoint all_disjoint]; split; exact I).
exact (entry_st_ok segs pc regs [] [fam_wcell gd nd] [] (mrestrict H mem) Hwf HF HD I).
Qed.
End r.

(* a writer's run up to its ret, by fam_run_hid *)
Ltac fam_wr_go tbl tblok Hwx HS :=
  lazymatch type of HS with st_ok ?segs ?E0 ?ss (restrict (w_H ?W0) ?ms) =>
    let r := eval vm_compute in (sym_runN segs tbl FUEL ss) in
    lazymatch r with (?ss', ?st) =>
      let Hrun := fresh "Hrun" in
      assert (Hrun : sym_runN segs tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
      apply (fam_run_hid segs tbl tblok Hwx W0 FUEL E0 ss ss' st ms _ _ HS Hrun I)
    end
  end.
(* the frame of the run: only the write cell's bytes may change *)
Ltac fam_wr_frame HFr :=
  let x := fresh "x" in let Hx := fresh "Hx" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros x Hx; apply HFr; intros (r & Hin & Hr); apply Hx;
  cbn [ss_mem fam_ss In] in Hin; destruct Hin as [<-|[]];
  unfold fam_wcell in Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia.

(* ==== 2. pure facts ==== *)
(* the 21 pairs of prh_pst's seven cells (#102: g_live, g_peak, g_count, g_fail_at, g_ran_out, g_most,
   g_own_ran_out), in order (1,2) (1,3) .. (1,7) (2,3) .. (6,7) (PwAllocSurf.v pas_sep7) *)
Lemma fam_sep7 : forall l1 l2 l3 l4 l5 l6 l7 : Z * Z, YG0f.pairwise zdisjoint [l1; l2; l3; l4; l5; l6; l7] ->
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

(* ==== 3. the core, parametric in the image ({PI} {PA}): everything but the byte run ==== *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
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
   TASK_SIZE, so a store to it keeps the kit's memnorm (fam_memnorm_frame below, over YAkMemnorm.memnorm) *)
Hypothesis PST_rw : forall a, Exists (in_zr a) prh_pst ->
  match find_segment segs a 1 with Some seg => seg_writable seg = true | None => True end.
Hypothesis PST_top : forallb (fun r => fst r + snd r <=? TASK_SIZE) prh_pst = true.

Lemma fam_cell_pst : forall g n a, In (g, n) prh_pst -> g <= a < g + n -> Exists (in_zr a) prh_pst.
Proof. intros g n a Hc Ha. apply Exists_exists. exists (g, n). split; [exact Hc | unfold in_zr; cbn [fst snd]; lia]. Qed.

(* a head byte of a ledger block is not a byte of a static: the head word is 8-aligned (a mod 16 = 0, cf_head_al) and
   the static is an 8-aligned cell of at most 8 bytes, so a shared byte makes the head's first byte the static's first
   byte, which PST_ok puts in the image and blk_img_x (it is a block byte) keeps out of it (PwAllocSurf.v
   pas_head_off, stated over the block's prh_hblock, which the caller takes from the named projection
   prh_ledger_blocks) *)
Lemma fam_head_off : forall ly S Hp W mem md g n a k i,
  ARx ly S Hp W mem md -> prh_hblock B ly S Hp W mem a k ->
  In (g, Z.of_nat n) prh_pst -> 0 <= i < 8 -> ~ (g <= a - cf_head + i < g + Z.of_nat n).
Proof.
intros ly S Hp W mem md g n a k i HAR Hb Hc Hi Hx.
pose proof (proj1 (Forall_forall _ _) PST_al _ Hc) as [Hg8 Hn8]. cbn [fst snd] in Hg8, Hn8.
destruct Hb as (Hk & Hbl & _ & Ha16 & _).
pose proof (@cf_head_al cp) as Hal. pose proof (@cf_head_nonneg cp) as Hh0.
assert (Eg : a - cf_head = g) by lia.
assert (Hreq : 0 < req_size (k + cf_head)) by (apply prh_req_size_pos; lia).
apply (blk_img_x segs B ARx LAWS ly S Hp W mem md (a - cf_head) (k + cf_head) g HAR Hbl ltac:(lia)).
exact (proj1 (PST_ok g (fam_cell_pst g (Z.of_nat n) g Hc ltac:(lia)))).
Qed.

(* a static off the written cell keeps its value *)
Lemma fam_glob_keep : forall (W : world segs) mem mem' g n g' n' v,
  In (g, Z.of_nat n) prh_pst -> In (g', Z.of_nat n') prh_pst -> zdisjoint (g, Z.of_nat n) (g', Z.of_nat n') ->
  (forall x : word, ~ (g <= bv_unsigned x < g + Z.of_nat n) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  val_mem segs (mrestrict (w_H W) mem) g' n' v -> val_mem segs (mrestrict (w_H W) mem') g' n' v.
Proof.
intros W mem mem' g n g' n' v Hc Hc' Hd Hfr Hv.
apply (prh_val_mem_keep _ _ _ _ _ Hv). intros k Hk.
assert (Hlow : 0 <= g' + Z.of_nat k < kLowMemEnd)
  by (apply pa_segs_low; exact (proj1 (PST_ok _ (fam_cell_pst g' (Z.of_nat n') (g' + Z.of_nat k) Hc' ltac:(lia))))).
apply (prh_mbyte_of_mrestrict (fun z => g <= z < g + Z.of_nat n)); [exact Hfr | unfold kLowMemEnd in Hlow; lia |].
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* the kit's memnorm (YAkMemnorm.v, which PRH_Base's fQmn uses) is kept by a change confined to [lo, hi) below
   TASK_SIZE that puts no byte at a read-only address (PwAllocSurf.v pas_memnorm_frame) *)
Lemma fam_memnorm_frame : forall (sg : list Segment) (m m' : word -> option byte) lo hi,
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

Lemma fam_in_live : In (pi_g_live, Z.of_nat pi_gz_live) prh_pst.
Proof. unfold prh_pst. cbn [In]. left. reflexivity. Qed.
Lemma fam_in_peak : In (pi_g_peak, Z.of_nat pi_gz_peak) prh_pst.
Proof. unfold prh_pst. cbn [In]. right. left. reflexivity. Qed.
Lemma fam_in_count : In (pi_g_count, Z.of_nat pi_gz_count) prh_pst.
Proof. unfold prh_pst. cbn [In]. right. right. left. reflexivity. Qed.
Lemma fam_in_fail : In (pi_g_fail, Z.of_nat pi_gz_fail) prh_pst.
Proof. unfold prh_pst. cbn [In]. right. right. right. left. reflexivity. Qed.
Lemma fam_in_ran : In (pi_g_ran_out, Z.of_nat pi_gz_ran_out) prh_pst.
Proof. unfold prh_pst. cbn [In]. right. right. right. right. left. reflexivity. Qed.
Lemma fam_in_most : In (pi_g_most, Z.of_nat pi_gz_most) prh_pst.
Proof. unfold prh_pst. cbn [In]. right. right. right. right. right. left. reflexivity. Qed.
Lemma fam_in_own : In (pi_g_own_ran_out, Z.of_nat pi_gz_own_ran_out) prh_pst.
Proof. unfold prh_pst. cbn [In]. right. right. right. right. right. right. left. reflexivity. Qed.

(* ---- the core: the kit's text from the byte run ---- *)
Lemma fam_most_core : fam_wr_run segs (pa_sigma AS_fuzz_alloc_most) pi_g_most pi_gz_most ->
  PRH_FnCheck.tfuzz_alloc_most_specX B ARx SK.
Proof.
intros RUN. unfold PRH_FnCheck.tfuzz_alloc_most_specX.
intros ly S Hp W regs mem md ch n Lam peak cnt fail ran most own [HPRE _] H10 Hn HL0.
pose proof HPRE as (HAR & Hra & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* the ledger's cells and its block part, by PRH_Base's named projections (ledger_proj) *)
pose proof (prh_ledger_live B ly S Hp W mem Lam peak cnt fail ran most own HL0) as GL.
pose proof (prh_ledger_peak B ly S Hp W mem Lam peak cnt fail ran most own HL0) as GP.
pose proof (prh_ledger_count B ly S Hp W mem Lam peak cnt fail ran most own HL0) as GC.
pose proof (prh_ledger_fail B ly S Hp W mem Lam peak cnt fail ran most own HL0) as GF.
pose proof (prh_ledger_ran B ly S Hp W mem Lam peak cnt fail ran most own HL0) as GR.
pose proof (PRH_Base.prh_ledger_own B ly S Hp W mem Lam peak cnt fail ran most own HL0) as [GO1 GO2].
pose proof (prh_ledger_bounds B ly S Hp W mem Lam peak cnt fail ran most own HL0) as (Rlp & Rpk & Rc & Rf & Rr).
pose proof (prh_ledger_nodup B ly S Hp W mem Lam peak cnt fail ran most own HL0) as HND.
pose proof (prh_ledger_blocks B ly S Hp W mem Lam peak cnt fail ran most own HL0) as HBK.
pose proof (prh_ledger_heads B ly S Hp W mem Lam peak cnt fail ran most own HL0) as HHD.
destruct (fam_sep7 _ _ _ _ _ _ _ PST_sep) as (Dlp & Dlc & Dlf & Dlr & Dlm & Dlo & Dpc & Dpf & Dpr & Dpm & Dpo &
  Dcf & Dcr & Dcm & Dco & Dfr & Dfm & Dfo & Drm & Dro & Dmo).
refine (RUN W regs mem md n _ Hra H10 Hn _).
intros regs' mem' X Hpr Hfr Hgr Hhid GM'.
unfold fpostm, fQmn, fpost, apost_base_x.
exists ly, S, Hp, regs', mem', (with_vm_backing (m_vm_lazy md) X md), 0.
split; [reflexivity|].
(* the journal: the entry's, then the one PST cell written (ajournal_x_pst_write) *)
assert (HJ0 := ajournal_x_init (SK := SK) segs B prh_pst ARx _ [] ly S Hp W regs mem md ch HPRE).
assert (Hfr' : forall x : word, ~ Exists (in_zr (bv_unsigned x)) prh_pst ->
  mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x).
{ intros x Hx. apply Hfr. intros Hin. apply Hx. exact (fam_cell_pst _ _ _ fam_in_most Hin). }
split; [exact (ajournal_x_pst_write (SK := SK) segs B prh_pst ARx LAWS pa_segs_low PST_ok
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0 Hfr' Hgr Hhid (same_but_materialized_wvb_any md X))|].
split; [exact Hpr|].
cbv beta. split.
{ split; [exact (fun h => h)|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  (* the statics at the end: g_most := n, the other six cells kept (prh_pst's cells are pairwise disjoint) *)
  assert (HG' : prh_glob W mem' (Ledger.lsum Lam) peak cnt fail ran n own).
  { unfold prh_glob.
    split; [exact (fam_glob_keep W mem mem' _ _ _ _ _ fam_in_most fam_in_live (prh_zdisjoint_sym _ _ Dlm) Hfr GL)|].
    split; [exact (fam_glob_keep W mem mem' _ _ _ _ _ fam_in_most fam_in_peak (prh_zdisjoint_sym _ _ Dpm) Hfr GP)|].
    split; [exact (fam_glob_keep W mem mem' _ _ _ _ _ fam_in_most fam_in_count (prh_zdisjoint_sym _ _ Dcm) Hfr GC)|].
    split; [exact (fam_glob_keep W mem mem' _ _ _ _ _ fam_in_most fam_in_fail (prh_zdisjoint_sym _ _ Dfm) Hfr GF)|].
    split; [exact (fam_glob_keep W mem mem' _ _ _ _ _ fam_in_most fam_in_ran (prh_zdisjoint_sym _ _ Drm) Hfr GR)|].
    split; [exact (conj GM' Hn)|].
    split; [exact (conj (fam_glob_keep W mem mem' _ _ _ _ _ fam_in_most fam_in_own Dmo Hfr GO1) GO2)|].
    repeat split; lia. }
  (* Lam's heads: off the written cell (fam_head_off) *)
  assert (HK : forall a k i, In (a, k) Lam -> 0 <= i < 8 ->
    mbyte segs (mrestrict (w_H W) mem') (a - cf_head + i) = mbyte segs (mrestrict (w_H W) mem) (a - cf_head + i)).
  { intros a k i Hin Hi.
    pose proof (proj1 (Forall_forall _ _) HBK (a, k) Hin) as Hb. cbv beta in Hb. cbn [fst snd] in Hb.
    pose proof Hb as (Hk & Hbl & _).
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hbl) as (_ & H4096 & Hceil & _).
    assert (Hreq : 0 < req_size (k + cf_head)) by (apply prh_req_size_pos; pose proof (@cf_head_nonneg cp); lia).
    assert (Hrng : 0 <= a - cf_head + i < 2 ^ 64) by lia.
    exact (prh_mbyte_of_mrestrict (fun z => pi_g_most <= z < pi_g_most + Z.of_nat pi_gz_most) _ _ _ _ _ Hfr Hrng
      (fam_head_off ly S Hp W mem md _ _ a k i HAR Hb fam_in_most Hi)). }
  assert (HLB : prh_lblocks B ly S Hp W mem' Lam)
    by exact (prh_lblocks_kept B ly S Hp W mem ly S Hp W mem' Lam (conj HND (conj HBK HHD)) HK
      (fun a k _ Hb => Hb) (Permutation_refl Hp)).
  exact (proj2 (prh_ledger_iff B ly S Hp W mem' Lam peak cnt fail ran n own) (conj HG' HLB)). }
(* memnorm is kept: the only change is inside the written cell, which is below TASK_SIZE and writable *)
{ intros HMN.
  assert (M1 : forall x : word, ~ (pi_g_most <= bv_unsigned x < pi_g_most + Z.of_nat pi_gz_most) -> mem' x = mem x).
  { intros x Hx. destruct (w_H W x) eqn:Ew; [exact (Hhid x Ew)|].
    pose proof (Hfr x Hx) as E. unfold mrestrict in E. rewrite Ew in E. exact E. }
  assert (M2 : pi_g_most + Z.of_nat pi_gz_most <= TASK_SIZE).
  { pose proof (proj1 (forallb_forall _ _) PST_top _ fam_in_most) as T. cbn [fst snd] in T. apply Z.leb_le in T.
    exact T. }
  assert (M3 : forall (x : word) b, pi_g_most <= bv_unsigned x < pi_g_most + Z.of_nat pi_gz_most -> mem' x = Some b ->
    YAkMemnorm.ro_addr segs x = false).
  { intros x b Hx _. pose proof (PST_rw _ (fam_cell_pst _ _ _ fam_in_most Hx)) as R.
    unfold YAkMemnorm.ro_addr.
    destruct (find_segment segs (bv_unsigned x) 1) as [seg|] eqn:Ef;
      [rewrite ?Ef in R; rewrite R; reflexivity | reflexivity]. }
  exact (fam_memnorm_frame segs mem mem' _ _ HMN M1 M2 M3). }
Qed.

End c.

(* a static's byte is writable in its segment, or in no segment (the image files compute it over their segments) *)
Definition fam_rw_b (segs : list Segment) (a : Z) : bool :=
  match find_segment segs a 1 with Some seg => seg_writable seg | None => true end.
