(* fuzz_strdup 0x82ce4 (fuzz/alloc.c:97-105) over fs.asan: the ASan walk of FSH_Fn_alloc.v's fuzz_strdup_spec.
   Code (23 instructions, dis 0x82ce4..0x82d3c; FSW_fuzz_strdup_tbl.v): prologue (frame 32: ra, s0, s1, s2 at
   sp + 24, 16, 8, 0); s0 := s; `jal __wrap_strlen` 0x82cfc; s1 := a0 + 1; a0 := s1; `jal fuzz_malloc` 0x82d08;
   s2 := a0; `beqz a0` 0x82d10; a0, a1, a2 := s2, s0, s1; `jal __asan_memcpy` 0x82d20; 0x82d24: a0 := s2; epilogue; ret.

   port-from:
   - control flow and the two arms: fs's released plain proof lib/Prog/fuzz_strdup_c.v:29-60 (ossv/recipes
     c8557374ad2e, plain 0x1416c): strlen, ONE fuzz_malloc, memcpy only on the non-NULL arm; the NULL arm returns 0
     with nothing copied and the statics' failing() update (fuzz_strdup_c.v:52-55); the non-NULL arm returns the new
     block holding cs ++ [0] (:56-62); the string home premise (:36-38) is cstr_kept here.
   - the walk's shape (entry state, runs, the program call, the return): a Theorem Labs lane's lib/A/FMW_check_as_written.v
     (a working branch) over FSW_K (fs's port of FMW_K), in fs's U form: FSW_K's U-form run step (fsw_aj_runU)
     for the five straight-line stretches, FSW_K's fsw_intrin_atU for the two runtime calls (strlen, memcpy).
   - the calls' resumed states: FSW_K's fsw_after_callFPU for the fuzz_malloc call (its journal composed under the
     caller's FP = FS_PSTAT_FP: the statics take fsw_fp_sub's `inFP FP a /\ in_img` arm) and fsw_resume_after_rtU for
     the two runtime calls (FSW_rres.v).
   - the string across the fuzz_malloc call: FSW_strkit.v (this lane).
   Structure: one lemma per stretch (sd_to_strlen, sd_strlen_step, sd_to_malloc, sd_malloc_step, sd_null_arm,
   sd_to_memcpy, sd_memcpy_step, sd_ret), chained by fuzz_strdup_holds.
   Named Section hypotheses (Section m; owners in the lane report): IMG (fs_img_facts), FS_ASTRLEN_A (strlen
   interceptor, ARU form), FS_AMEMCPY_A (__asan_memcpy, ARU form), FS_FUZZ_MALLOC_A (fuzz_malloc_spec; no CTX binder
   since stage 1 of the fold, owner 05:00Z / a Theorem Labs lane 05:11Z).
   Rule 24: no released ASan proof of fuzz_strdup exists (a Theorem Labs lane's proof-index lookup, 2026-10-28T21:12Z);
   lemma names grepped on origin/main, ossv/recipes, ossv/candidates, release/pau-projects-recipes: none of this
   file's or FSW_strkit.v's names exist there. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSH_Fn_alloc FSW_K FSW_K3 FSW_rres FSW_strkit
FSW_fuzz_strdup_tbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* the four saved registers of the entry, read back as the resumed states' extra atoms 32 .. 35 (sd_cs) *)
Definition sd_extra (regs : bvmap 5 word) : list word :=
  [YK11.getr regs 1; YK11.getr regs 8; YK11.getr regs 9; YK11.getr regs 18].
(* what the callee-saved registers hold at `ret`: sp back up by the frame, s0 / s1 / s2 reloaded, the rest untouched *)
Definition sd_expect (r : bv 5) : sv :=
  match bv_unsigned r with
  | 2 => SOff 2 32 | 8 => SOff 33 0 | 9 => SOff 34 0 | 18 => SOff 35 0
  | z => SOff (Z.to_nat z) 0
  end.
(* the callee-saved registers fuzz_strdup does not use hold their entry values at a resumed state *)
Definition sd_kept (regs regsR : bvmap 5 word) : Prop :=
  forall r, acallee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 ->
  YK11.getr regsR (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r).

Lemma sd_tbl_ret : clookup sd_tbl 0x82d3c = Some RET_WORD_r.
Proof. vm_compute. reflexivity. Qed.

(* fs.asan's alloc.c statics are image bytes; a read-only byte (in_roP) is an image byte and none of the statics *)
Lemma sd_pstat_img : forall a, inFP FS_PSTAT_FP a -> in_img tfibsegs a.
Proof.
intros a (r & Hr & Ha).
assert (Hb : forallb (fun r : Z * Z => seg_covers (fst r) (snd r - fst r)) FS_PSTAT_FP = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) Hb r Hr) as H. exact (seg_covers_img _ _ a H ltac:(lia)).
Qed.
Lemma sd_relro_img : forall a, FS_RLO <= a < FS_RHI -> in_img tfibsegs a.
Proof.
intros a Ha. assert (H : seg_covers FS_RLO (FS_RHI - FS_RLO) = true) by (vm_compute; reflexivity).
exact (seg_covers_img _ _ a H ltac:(lia)).
Qed.
Lemma sd_ro_img : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> in_img tfibsegs a.
Proof.
intros a [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (sd_relro_img a Hr)].
Qed.
Lemma sd_ro_not_pstat : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP FS_PSTAT_FP a.
Proof.
intros a Hro (r & Hr & Ha).
assert (Hb : forallb (fun r : Z * Z => (FS_RHI <=? fst r) &&
  forallb (fun s => seg_writable s || (snd r <=? Z.of_N (seg_base s)) ||
                    (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? fst r)) tfibsegs) FS_PSTAT_FP = true)
  by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) Hb r Hr) as H. cbv beta in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1.
destruct Hro as [(sg & Hsg & Hw & Hs) | Hrl]; [|lia].
pose proof (proj1 (forallb_forall _ _) H2 sg Hsg) as H3. cbv beta in H3. rewrite Hw in H3. cbn [orb] in H3.
apply orb_prop in H3 as [H3|H3]; apply Z.leb_le in H3; lia.
Qed.
(* two ranges that share no point are ordered *)
Lemma sd_range_order : forall p a q c, 0 < a -> 0 < c ->
  (forall x, p <= x < p + a -> ~ (q <= x < q + c)) -> p + a <= q \/ q + c <= p.
Proof.
intros p a q c Ha Hc H. destruct (Z_le_gt_dec (p + a) q) as [L|L]; [left; exact L|].
destruct (Z_le_gt_dec (q + c) p) as [L'|L']; [right; exact L'|].
exfalso. apply (H (Z.max p q)); lia.
Qed.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* the epilogue from a resumed state (after memcpy, or the beqz-taken arm after fuzz_malloc): the run to `ret`, the
   return to the entry ra, and fpostU with the journal the walk has built. Generic in the starting symbolic state, whose
   run is checked by vm_compute at the use site. *)
Lemma sd_ret : forall ly S U W regs mem md lyR SR UR WR regsR ms mdR k ss ssf stf v
  (Q : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok tfibsegs (Ereg regsR (sd_extra regs)) ss (restrict (w_H WR) ms) ->
  ss_mem ss = [fstk_ret 32 sd_cs] ->
  sym_runN tfibsegs sd_tbl FUEL ss = (ssf, stf) -> match stf with RS_ecall => False | _ => True end ->
  ss_pc ssf = 0x82d3c -> ss_resv ssf = None ->
  sr_get (ss_regs ssf) 1%bv = SOff 32 0 ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ssf) r) (sd_expect r)) CALLEE_SAVED = true ->
  sv_denot (Ereg regsR (sd_extra regs)) (sr_get (ss_regs ssf) 10%bv) = w64 v ->
  ARU tfibsegs B lyR SR UR WR (ms_mem ms) mdR ->
  ajournal tfibsegs B STK_fuzz_strdup (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md [] lyR SR WR
    (unpoison UR (ms_mem ms)) mdR k ->
  spZ regsR = spZ regs - 32 -> sd_kept regs regsR -> YK0s.ret_ok (YK11.getr regs 1) ->
  (forall regsF memF mdF, same_below (ms_mem ms) memF alloc_ceiling -> YK11.getr regsF 10 = w64 v ->
     Q lyR SR WR regsF memF mdF) ->
  SRr tfibsegs WR (mkCfg ms mdR) (apost_baseU tfibsegs B STK_fuzz_strdup FS_PSTAT_FP regs ly S W mem md k U UR Q).
Proof.
intros ly S U W regs mem md lyR SR UR WR regsR ms mdR k ss ssf stf v Q HS Hmem Hrun Hst Hpc Hrv H1 Hcs H10 HARU HJ
  Esp Hkept Hra HQ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & _). assert (FS : STK_fuzz_strdup = 16448) by reflexivity.
set (E := Ereg regsR (sd_extra regs)) in *.
assert (E2 : bv_unsigned (ew E 2) = spZ regs - 32) by (unfold E; rewrite (ew_Ereg_nat regsR _ 2 2%bv eq_refl); exact Esp).
eapply (fsw_run_AJU B sd_tbl sd_tbl_ok WR FUEL E ss ssf stf ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS Hrun Hst HARU HJ).
all: first [ solve [ rewrite Hmem; eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -32); first [solve [reflexivity] | solve [exact E2] | solve [cbn; lia] | solve [apply awr_ok_nil]] ] | idtac ].
intros msf mat HSf HJf HARUf HF HFr HG. clear HS Hrun HJ HARU.
rewrite ?wvb_collapse in HJf, HARUf.
assert (SB : same_below (ms_mem ms) (ms_mem msf) alloc_ceiling).
{ rewrite Hmem in HF. apply (same_below_frame1 E (fstk_ret 32 sd_cs) (ms_mem ms) (ms_mem msf) alloc_ceiling HF);
    first [solve [lia] | idtac].
  cbn [fstk_ret YP09.r_base YP09.r_wlo base_val]. rewrite E2. lia. }
assert (R1F : YK11.getr (ms_regs msf) 1%bv = YK11.getr regs 1%bv).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H WR) E ssf msf 1%bv HSf), H1, fsw_SOff0.
  unfold E. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity. }
assert (R10F : YK11.getr (ms_regs msf) 10%bv = w64 v) by (rewrite (st_ok_restrict_reg tfibsegs (w_H WR) E ssf msf 10%bv HSf); exact H10).
eapply (SRr_ret_at tfibsegs sd_tbl sd_tbl_ok fs_wx WR E ssf msf);
  first [solve [exact HSf] | solve [exact Hrv] | solve [rewrite Hpc; exact sd_tbl_ret] | idtac].
intros mat2.
assert (Hpc' : v_jalr (YK11.getr (ms_regs msf) 1) 0 = YK11.getr regs 1) by (rewrite R1F; exact Hra).
rewrite Hpc'. unfold apost_baseU, fpostU.
exists lyR, SR. do 3 eexists.
split; [reflexivity|].
split; [apply (ajournal_materialize tfibsegs B LAWS fs_segs_low); exact HJf|].
split; [exact (proj1 (proj2 HARUf))|]. split; [exact (proj2 (proj2 HARUf))|].
split.
{ apply (fsw_preserved _ E ssf msf regs sd_expect HSf Hcs).
  intros r Hr. cbv [CALLEE_SAVED In] in Hr.
  repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
  lazymatch goal with |- sv_denot _ (sd_expect ?q) = _ =>
    let e := eval vm_compute in (sd_expect q) in change (sd_expect q) with e end;
  first
  [ apply fsw_sp_back; exact E2
  | rewrite fsw_SOff0; unfold E; rewrite ?ew_Ereg_extra; reflexivity
  | rewrite fsw_SOff0; unfold E;
    lazymatch goal with |- ew _ ?n = YK11.getr _ ?q =>
      rewrite (ew_Ereg_nat regsR _ n q eq_refl);
      let z := eval vm_compute in (bv_unsigned q) in
      pose proof (Hkept z ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hk;
      exact Hk end ]. }
apply HQ; [exact SB | exact R10F].
Qed.

(* the NULL arm after fuzz_malloc (alloc.c:102 `if (d)` false): from the state resumed at 0x82d0c with a0 = 0, the
   run to `beqz a0`, the taken branch, and the epilogue *)
Lemma sd_null_arm : forall ly S Up W regs mem md ly2 S2 Up2 W2 regs2 mem2 md2 k
  (Q : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok tfibsegs (Ereg regs2 (sd_extra regs)) (fss_ret RA_SD_MALLOC 32 sd_cs)
    (restrict (w_H W2) (YK11.mkst regs2 (Z_to_bv 64 RA_SD_MALLOC) mem2 (YK11.seg_rom tfibsegs))) ->
  ARU tfibsegs B ly2 S2 Up2 W2 mem2 md2 ->
  ajournal tfibsegs B STK_fuzz_strdup (spZ regs) FS_PSTAT_FP ly S W (unpoison Up mem) md [] ly2 S2 W2
    (unpoison Up2 mem2) md2 k ->
  spZ regs2 = spZ regs - 32 -> sd_kept regs regs2 -> YK0s.ret_ok (YK11.getr regs 1) ->
  YK11.getr regs2 10 = w64 0 ->
  (forall regsF memF mdF, same_below mem2 memF alloc_ceiling -> YK11.getr regsF 10 = w64 0 ->
     Q ly2 S2 W2 regsF memF mdF) ->
  SRr tfibsegs W2 (mkCfg (YK11.mkst regs2 (Z_to_bv 64 RA_SD_MALLOC) mem2 (YK11.seg_rom tfibsegs)) md2)
    (apost_baseU tfibsegs B STK_fuzz_strdup FS_PSTAT_FP regs ly S W mem md k Up Up2 Q).
Proof.
intros ly S Up W regs mem md ly2 S2 Up2 W2 regs2 mem2 md2 k Q HS HARU HJ Esp Hkept Hra H10 HQ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & _). assert (FS : STK_fuzz_strdup = 16448) by reflexivity.
assert (E2 : bv_unsigned (ew (Ereg regs2 (sd_extra regs)) 2) = spZ regs - 32)
  by (rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl); exact Esp).
assert (U10 : U (Ereg regs2 (sd_extra regs)) (SOff 10 0) = 0)
  by (apply U_atom; [rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl); exact H10 | lia]).
assert (UZ : U (Ereg regs2 (sd_extra regs)) (SLit 0) = 0) by (apply U_lit; lia).
fsw_aj_runU sd_tbl_ok HS HJ HARU.
all: first [ solve [ fsw_awr_ret E2 32 ] | idtac ].
assert (SB1 : same_below mem2 (ms_mem ms) alloc_ceiling).
{ unfold fss_ret in HF. cbn [ss_mem] in HF.
  apply (same_below_frame1 _ (fstk_ret 32 sd_cs) mem2 (ms_mem ms) alloc_ceiling HF); first [solve [lia] | idtac].
  cbn [fstk_ret YP09.r_base YP09.r_wlo base_val]. rewrite E2. lia. }
eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 10 0) (b := SLit 0) (1 := HS).
(* the two branch continuations of SRr_sym_branch: taken (a0 = 0, the NULL arm), then not taken (refuted) *)
- intros Hb HS3.
  eapply (sd_ret ly S Up W regs mem md ly2 S2 Up2 W2 regs2 ms _ k); [exact HS3 | reflexivity | vm_compute; reflexivity
    | exact I | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | | exact HARU | exact HJ
    | exact Esp | exact Hkept | exact Hra |].
  + lazymatch goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end.
    rewrite fsw_SOff0, (ew_Ereg_nat regs2 _ 10 10%bv eq_refl). exact H10.
  + intros regsF memF mdF SBF HF10. apply HQ; [exact (same_below_trans _ _ _ _ SB1 SBF) | exact HF10].
- intros Hb _. exfalso. rewrite branch_eq_U, U10, UZ in Hb. discriminate Hb.
Qed.

(* ---- the source string across the fuzz_malloc call ---- *)
(* no byte of a kept string lies in the block fuzz_malloc appends: a block home is disjoint from it (AR's pairwise
   disjoint blocks), a table home is image bytes and the new block holds none *)
Lemma sd_str_off_new : forall ly S ly2 S2 W2 m2 md2 p l res nn (Up : list (Z * Z)),
  AR tfibsegs B ly2 S2 W2 m2 md2 -> ablocks B ly2 S2 = ablocks B ly S ++ [(res - HEAD, nn + HEAD)] -> 0 <= nn ->
  cstr_kept B ly S Up p l ->
  forall x, p <= x < p + Z.of_nat (length l) + 1 -> ~ (res - HEAD <= x < res - HEAD + (nn + HEAD)).
Proof.
intros ly S ly2 S2 W2 m2 md2 p l res nn Up HAR Eab Hnn Hk x Hx Hxn.
assert (Rq : req_size (nn + HEAD) = nn + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (nn + 16) 0); lia).
assert (Hnew : In (res - HEAD, nn + HEAD) (ablocks B ly2 S2)) by (rewrite Eab; apply in_or_app; right; left; reflexivity).
destruct Hk as [(b & m & Hin & Hb & Hbm & _) | Htbl].
- apply in_split in Hin as (l1 & l2 & El).
  assert (E2 : ablocks B ly2 S2 = l1 ++ (b, m) :: l2 ++ (res - HEAD, nn + HEAD) :: []).
  { rewrite Eab, El. rewrite <- app_assoc. reflexivity. }
  pose proof (sep_blocks_pos tfibsegs B LAWS ly2 S2 W2 m2 md2 (b, m) (res - HEAD, nn + HEAD) l1 l2 [] HAR E2) as D.
  unfold zdisjoint, block_rng in D. cbn [fst snd] in D. rewrite Rq in D.
  pose proof (req_size_pos m ltac:(lia)) as Rm. lia.
- assert (Hi : in_img tfibsegs x).
  { destruct Htbl as [Hs | (ps & Hf & ->)]; [exact (fs_ro_strs_img p l x Hs Hx) | exact (fs_sn_fmts_img p ps x Hf Hx)]. }
  exact (blk_img tfibsegs B LAWS ly2 S2 W2 m2 md2 (res - HEAD) (nn + HEAD) x HAR Hnew ltac:(rewrite Rq; lia) Hi).
Qed.
(* so every range of U ++ [new head] is one of U or misses the string (cstr_ok_keptU's premise) *)
Lemma sd_heads_off : forall ly S ly2 S2 W2 m2 md2 (Up : list (Z * Z)) p l res nn,
  AR tfibsegs B ly2 S2 W2 m2 md2 -> ablocks B ly2 S2 = ablocks B ly S ++ [(res - HEAD, nn + HEAD)] -> 0 <= nn ->
  cstr_kept B ly S Up p l ->
  forall r, In r (Up ++ [(res - HEAD, HEAD)]) -> In r Up \/ fst r + snd r <= p \/ p + Z.of_nat (length l) + 1 <= fst r.
Proof.
intros ly S ly2 S2 W2 m2 md2 Up p l res nn HAR Eab Hnn Hk r Hr.
apply in_app_or in Hr as [Hr | [<- | []]]; [left; exact Hr | right]. cbn [fst snd].
pose proof (sd_str_off_new ly S ly2 S2 W2 m2 md2 p l res nn Up HAR Eab Hnn Hk) as H.
destruct (sd_range_order p (Z.of_nat (length l) + 1) (res - HEAD) HEAD ltac:(lia) ltac:(unfold HEAD; lia)) as [L|L];
  [| right; lia | left; lia].
intros x Hx Hx'. apply (H x ltac:(lia)). unfold HEAD in *. lia.
Qed.
(* and the copy's destination [res, res + nn) and its source [p, p + nn) are disjoint (aintrin_realizesU OCpy) *)
Lemma sd_cpy_disj : forall ly S ly2 S2 W2 m2 md2 p l res (Up : list (Z * Z)),
  AR tfibsegs B ly2 S2 W2 m2 md2 ->
  ablocks B ly2 S2 = ablocks B ly S ++ [(res - HEAD, Z.of_nat (length l) + 1 + HEAD)] ->
  cstr_kept B ly S Up p l ->
  res + (Z.of_nat (length l) + 1) <= p \/ p + (Z.of_nat (length l) + 1) <= res.
Proof.
intros ly S ly2 S2 W2 m2 md2 p l res Up HAR Eab Hk.
pose proof (sd_str_off_new ly S ly2 S2 W2 m2 md2 p l res _ Up HAR Eab ltac:(lia) Hk) as H.
destruct (sd_range_order p (Z.of_nat (length l) + 1) res (Z.of_nat (length l) + 1) ltac:(lia) ltac:(lia)) as [L|L];
  [| right; exact L | left; exact L].
intros x Hx Hx'. apply (H x ltac:(lia)). unfold HEAD in *. lia.
Qed.
(* the read-only view rides through a journal at FS_PSTAT_FP: read-only bytes are image bytes outside the statics, and
   below the shadow, where the unpoisoned reading is the machine's *)
Lemma sd_arodata_kept : forall STK sp0 ly S Up W mem md own lyc Sc Uc Wc memc mdc k,
  ARU tfibsegs B ly S Up W mem md -> ARU tfibsegs B lyc Sc Uc Wc memc mdc ->
  ajournal tfibsegs B STK sp0 FS_PSTAT_FP ly S W (unpoison Up mem) md own lyc Sc Wc (unpoison Uc memc) mdc k ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H Wc) memc).
Proof.
intros STK sp0 ly S Up W mem md own lyc Sc Uc Wc memc mdc k H0 H1 HJ HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
pose proof (sd_ro_img a Hro) as Hi. pose proof (fsk_segs_img a Hi) as Hl. unfold FS_IMG_END in Hl.
assert (Happ : a < SHADOW_OFF \/ kHighMemBeg <= a) by (left; unfold SHADOW_OFF; lia).
rewrite <- (aview_at tfibsegs (w_H Wc) (unpoison Uc memc) memc a (unpoison_app B lyc Sc Uc Wc memc mdc a H1 ltac:(lia) Happ)).
rewrite (F3 a Hi Ho He (sd_ro_not_pstat a Hro)).
- rewrite (aview_at tfibsegs (w_H W) (unpoison Up mem) mem a (unpoison_app B ly S Up W mem md a H0 ltac:(lia) Happ)).
  exact (HR a Hro Ho He).
- apply fp_spares_closed. apply sink_closed_pos. repeat constructor; cbn; lia.
Qed.
(* cstr_ok of the source after the fuzz_malloc call, from cstr_kept (FSW_strkit.cstr_ok_keptU) *)
Lemma sd_cstr_after : forall STK sp0 ly S Up W mem md ly2 S2 W2 mem2 md2 k p l res nn,
  fs_img_facts tfibsegs B ->
  ARU tfibsegs B ly S Up W mem md -> ARU tfibsegs B ly2 S2 (Up ++ [(res - HEAD, HEAD)]) W2 mem2 md2 ->
  ajournal tfibsegs B STK sp0 FS_PSTAT_FP ly S W (unpoison Up mem) md [] ly2 S2 W2
    (unpoison (Up ++ [(res - HEAD, HEAD)]) mem2) md2 k ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem) ->
  ablocks B ly2 S2 = ablocks B ly S ++ [(res - HEAD, nn + HEAD)] -> 0 <= nn ->
  cstr_kept B ly S Up p l -> cstr_ok tfibsegs W mem p l -> cstr_ok tfibsegs W2 mem2 p l.
Proof.
intros STK sp0 ly S Up W mem md ly2 S2 W2 mem2 md2 k p l res nn IMG H0 H2 HJ HR Eab Hnn Hk Hc.
pose proof H2 as (HAR2 & OK2 & PO2).
apply (cstr_ok_keptU B STK sp0 FS_PSTAT_FP ly S Up W mem md [] ly2 S2 (Up ++ [(res - HEAD, HEAD)]) W2 mem2 md2 k p l
  IMG H0 HJ OK2 PO2);
  first [ solve [exact sd_pstat_img] | solve [exact (sd_arodata_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0 H2 HJ HR)]
        | solve [exact Hk] | solve [exact (sd_heads_off ly S ly2 S2 W2 _ md2 Up p l res nn HAR2 Eab Hnn Hk)]
        | solve [exact Hc] | solve [intros x Hx; rewrite Eab; apply in_or_app; left; exact Hx] ].
Qed.

(* ---- the memcpy call's destination: the new block's user bytes (aintrin_realizesU's dest_ok / range premises) ---- *)
Lemma sd_dest_bytes : forall ly2 S2 Up2 W2 memC md2 res nn,
  ARU tfibsegs B ly2 S2 Up2 W2 memC md2 -> In (res - HEAD, nn + HEAD) (ablocks B ly2 S2) -> 0 <= nn ->
  forall a, res <= a < res + nn ->
  apresent (w_H W2) memC a /\ ~ aowned B ly2 S2 a /\ 4096 <= a < alloc_ceiling.
Proof.
intros ly2 S2 Up2 W2 memC md2 res nn H Hin Hnn a Ha.
pose proof H as (HAR & _ & _).
assert (Rq : req_size (nn + HEAD) = nn + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (nn + 16) 0); lia).
destruct (al_blocks _ _ LAWS ly2 S2 W2 (unpoison Up2 memC) md2 (res - HEAD) (nn + HEAD) HAR Hin)
  as (_ & H4096 & Hceil & Happ & Hpres & _). rewrite Rq in Hceil, Happ, Hpres.
destruct (Hpres a ltac:(unfold HEAD in *; lia)) as ((Hh & b & Hb) & Hno).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Happ' : a < SHADOW_OFF \/ kHighMemBeg <= a).
{ destruct Happ as [_ [Hl | [Hh1 _]]]; [left | right]; unfold kLowShadowBeg, SHADOW_OFF, HEAD in *; lia. }
split; [|split; [exact Hno | unfold HEAD in *; lia]].
split; [exact Hh|]. exists b. rewrite <- (unpoison_app B ly2 S2 Up2 W2 memC md2 a H ltac:(unfold HEAD in *; lia) Happ'). exact Hb.
Qed.
Lemma sd_dest_hull : forall ly2 S2 Up2 W2 memC md2 res nn,
  ARU tfibsegs B ly2 S2 Up2 W2 memC md2 -> In (res - HEAD, nn + HEAD) (ablocks B ly2 S2) -> 0 < nn ->
  shadow_hull_vis (aview tfibsegs (w_H W2) memC) res nn.
Proof.
intros ly2 S2 Up2 W2 memC md2 res nn H Hin Hnn s Hs.
pose proof H as (HAR & _ & PO).
assert (Rq : req_size (nn + HEAD) = nn + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (nn + 16) 0); lia).
apply (aview_unpoison_vis Up2 W2 memC s PO).
apply (shadow_hull_vis_of_block tfibsegs B LAWS ly2 S2 W2 (unpoison Up2 memC) md2 (res - HEAD) (nn + HEAD) res nn HAR Hin);
  first [solve [unfold HEAD; lia] | solve [rewrite Rq; unfold HEAD; lia] | solve [exact Hnn] | solve [exact Hs]].
Qed.
Lemma sd_dest_amem : forall ly2 S2 W2 m md2 res nn,
  AR tfibsegs B ly2 S2 W2 m md2 -> In (res - HEAD, nn + HEAD) (ablocks B ly2 S2) -> 0 <= nn -> amem_range res nn.
Proof.
intros ly2 S2 W2 m md2 res nn HAR Hin Hnn.
assert (Rq : req_size (nn + HEAD) = nn + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (nn + 16) 0); lia).
apply (amem_range_of_block tfibsegs B LAWS ly2 S2 W2 m md2 (res - HEAD) (nn + HEAD) res nn HAR Hin);
  first [solve [unfold HEAD; lia] | solve [rewrite Rq; unfold HEAD; lia]].
Qed.
(* range_addressable over a frame that keeps everything below alloc_ceiling (the shadow of application bytes is there) *)
Lemma sd_range_addressable_below : forall (H : word -> bool) m m' p n,
  same_below m m' alloc_ceiling -> 0 <= p -> p + n <= alloc_ceiling ->
  range_addressable (aview tfibsegs H m) SHADOW_OFF p n -> range_addressable (aview tfibsegs H m') SHADOW_OFF p n.
Proof.
intros H m m' p n SB Hp Hn Hra x Hx. destruct (Hra x Hx) as (v & Hv & Hok). exists v. split; [|exact Hok].
pose proof asan_consts as (C1 & _).
rewrite (aview_below H m m' alloc_ceiling); first [solve [exact Hv] | solve [exact SB] | idtac].
unfold shadow_of_addr, SHADOW_OFF. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_le_upper_bound x 8 (2 ^ 47) ltac:(lia) ltac:(lia)). lia.
Qed.

(* ---- the arm-2 post from the memcpy post (FSupoisonU.aintrin_realizesU OCpy) ---- *)
Lemma sd_mbyte_of_aview2 : forall (H H' : word -> bool) (m m' : word -> option byte) a a',
  aview tfibsegs H' m' a' = aview tfibsegs H m a -> mbyte tfibsegs (mrestrict H' m') a' = mbyte tfibsegs (mrestrict H m) a.
Proof.
intros H H' m m' a a' E. unfold aview in E.
destruct (mbyte tfibsegs (mrestrict H' m') a') as [b'|], (mbyte tfibsegs (mrestrict H m) a) as [b|]; cbn in E;
  try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma sd_garr8_shift : forall (m m' : word -> option byte) p q l,
  garr8 tfibsegs m p l -> (forall j, 0 <= j < Z.of_nat (length l) -> mbyte tfibsegs m' (q + j) = mbyte tfibsegs m (p + j)) ->
  garr8 tfibsegs m' q l.
Proof.
intros m m' p q l H Hm j Hj. destruct (H j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk. assert (k = 0%nat) as -> by lia. rewrite !Z.add_0_r.
rewrite (Hm (Z.of_nat j) ltac:(lia)). pose proof (Hv 0%nat Hk) as E. rewrite Z.add_0_r in E. exact E.
Qed.
Lemma sd_q2 : forall ly S ly2 S2 Up W2 m2 md2 memC memD spC live peak cnt fail p l res,
  AR tfibsegs B ly2 S2 W2 m2 md2 ->
  ablocks B ly2 S2 = ablocks B ly S ++ [(res - HEAD, Z.of_nat (length l) + 1 + HEAD)] ->
  fs_heads B ly2 S2 (Up ++ [(res - HEAD, HEAD)]) -> 4096 + HEAD <= res ->
  fs_rblock tfibsegs B ly2 S2 W2 memC res (Z.of_nat (length l) + 1) ->
  fs_glob tfibsegs W2 memC (live + (Z.of_nat (length l) + 1)) (Z.max peak (live + (Z.of_nat (length l) + 1)))
    (cnt + 1) fail ->
  cstr_ok tfibsegs W2 memC p l ->
  (forall i, 0 <= i < Z.of_nat (length l) + 1 -> aview tfibsegs (w_H W2) memD (res + i) = aview tfibsegs (w_H W2) memC (p + i)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (res <= a < res + (Z.of_nat (length l) + 1)) -> ~ (spC - ESTACK <= a < spC) ->
     aview tfibsegs (w_H W2) memD a = aview tfibsegs (w_H W2) memC a) ->
  alloc_ceiling <= spC - ESTACK ->
  forall regsF memF (mdF : Model), same_below memD memF alloc_ceiling -> YK11.getr regsF 10 = w64 res ->
  YK11.getr regsF 10 = w64 res /\ 4096 + HEAD <= res /\
  ablocks B ly2 S2 = ablocks B ly S ++ [(res - HEAD, Z.of_nat (length l) + 1 + HEAD)] /\
  fs_heads B ly2 S2 (Up ++ [(res - HEAD, HEAD)]) /\
  fs_rblock tfibsegs B ly2 S2 W2 memF res (Z.of_nat (length l) + 1) /\
  zbytes_at tfibsegs W2 memF res (l ++ [0]) /\
  fs_glob tfibsegs W2 memF (live + (Z.of_nat (length l) + 1)) (Z.max peak (live + (Z.of_nat (length l) + 1)))
    (cnt + 1) fail.
Proof.
intros ly S ly2 S2 Up W2 m2 md2 memC memD spC live peak cnt fail p l res HAR Eab FH Hres Hrb HG Hc Hcpy Hfr Hwin
  regsF memF mdF SB H10.
pose proof asan_consts as (C1 & _).
set (nn := Z.of_nat (length l) + 1) in *.
assert (Rq : req_size (nn + HEAD) = nn + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (nn + 16) 0); lia).
assert (Hnew : In (res - HEAD, nn + HEAD) (ablocks B ly2 S2)) by (rewrite Eab; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly2 S2 W2 m2 md2 (res - HEAD) (nn + HEAD) HAR Hnew) as (_ & H4096 & Hceil & _).
rewrite Rq in Hceil.
(* memC -> memD outside the copy and the window; below alloc_ceiling that is everything but the copy *)
assert (KD : forall a, 0 <= a < alloc_ceiling -> ~ (res <= a < res + nn) ->
  aview tfibsegs (w_H W2) memD a = aview tfibsegs (w_H W2) memC a) by (intros a Ha Hn; apply Hfr; [lia | exact Hn | lia]).
split; [exact H10|]. split; [exact Hres|]. split; [exact Eab|]. split; [exact FH|].
split.
{ destruct Hrb as (Hin & H16 & Hn & Hv). split; [exact Hin|]. split; [exact H16|]. split; [exact Hn|].
  apply (val_mem_below (w_H W2) memD memF alloc_ceiling _ 8 _ SB); first [solve [unfold HEAD in *; lia] | idtac].
  apply (val_mem_kept tfibsegs (w_H W2) (w_H W2) memC memD); first [solve [exact Hv] | idtac].
  intros k Hk. apply KD; unfold HEAD in *; lia. }
split.
{ unfold zbytes_at. apply (garr8_frame tfibsegs (mrestrict (w_H W2) memD));
    first [ solve [destruct Hc as ((Hg & _) & _); apply (sd_garr8_shift _ _ p res (l ++ [0]) Hg);
                   intros j Hj; rewrite length_app in Hj; cbn [length] in Hj;
                   apply sd_mbyte_of_aview2; apply Hcpy; unfold nn; lia]
          | solve [intros a Ha; rewrite length_app in Ha; cbn [length] in Ha;
                   apply (mbyte_below _ memD memF alloc_ceiling a SB); unfold nn, HEAD in *; lia] ]. }
apply (fs_glob_below W2 memD memF _ _ _ _ SB).
destruct HG as (G1 & G2 & G3 & G4 & R).
assert (GI : forall g, In (g, g + 8) FS_PSTAT_FP -> forall k, 0 <= k < 8 -> ~ (res <= g + k < res + nn)).
{ intros g Hg k Hk Hgk. pose proof (sd_pstat_img (g + k) (inFP_FS_PSTAT_FP g Hg (g + k) ltac:(lia))) as Hi.
  exact (blk_img tfibsegs B LAWS ly2 S2 W2 m2 md2 (res - HEAD) (nn + HEAD) (g + k) HAR Hnew ltac:(rewrite Rq; unfold HEAD; lia) Hi). }
assert (VK : forall g v, In (g, g + 8) FS_PSTAT_FP -> val_mem tfibsegs (mrestrict (w_H W2) memC) g 8 v ->
  val_mem tfibsegs (mrestrict (w_H W2) memD) g 8 v).
{ intros g v Hg Hv. apply (val_mem_kept tfibsegs (w_H W2) (w_H W2) memC memD); first [solve [exact Hv] | idtac].
  intros k Hk. apply KD; [| exact (GI g Hg k ltac:(lia))].
  assert (Hb : forallb (fun r : Z * Z => (0 <=? fst r) && (snd r <=? FS_IMG_END)) FS_PSTAT_FP = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) Hb _ Hg) as Hgb. cbn beta in Hgb. apply andb_prop in Hgb as [Hg1 Hg2].
  apply Z.leb_le in Hg1. apply Z.leb_le in Hg2. cbn [fst snd] in Hg1, Hg2. unfold FS_IMG_END in Hg2. lia. }
unfold fs_glob, fs_glob_at.
split; [apply VK; [unfold FS_PSTAT_FP, G_LIVE; cbn; tauto | exact G1]|].
split; [apply VK; [unfold FS_PSTAT_FP, G_PEAK; cbn; tauto | exact G2]|].
split; [apply VK; [unfold FS_PSTAT_FP, G_COUNT; cbn; tauto | exact G3]|].
split; [apply VK; [unfold FS_PSTAT_FP, G_FAIL; cbn; tauto | exact G4]|].
exact R.
Qed.

(* ---- the fuzz_malloc call at 0x82d08: the callee's fpreU from the caller's journal (frame 32 below the entry sp; the
   callee's chain is empty because s0 holds the string pointer, which is below alloc_ceiling) ---- *)
Lemma sd_malloc_pre : forall ly S Up W regs mem md lyc Sc Wc regsM memM mdM k,
  ARU tfibsegs B ly S Up W mem md -> ARU tfibsegs B lyc Sc Up Wc memM mdM ->
  ajournal tfibsegs B STK_fuzz_strdup (spZ regs) FS_PSTAT_FP ly S W (unpoison Up mem) md [] lyc Sc Wc
    (unpoison Up memM) mdM k ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem) ->
  spZ regsM = spZ regs - 32 -> YK11.getr regsM 1 = Z_to_bv 64 RA_SD_MALLOC ->
  YK11.getr regsM 3 = w64 (as_gp B) -> YK11.getr regsM 4 = w64 (as_tp B) -> s0Z regsM < alloc_ceiling ->
  fpreU tfibsegs B STK_fuzz_malloc lyc Sc Up Wc regsM memM mdM [].
Proof.
intros ly S Up W regs mem md lyc Sc Wc regsM memM mdM k H0 HC HJ HR Esp R1 R3 R4 Hs0.
pose proof HC as (_ & OK & PO).
assert (FS : STK_fuzz_strdup = 16448) by reflexivity. assert (FM : STK_fuzz_malloc = 16416) by reflexivity.
split; [|exact (sd_arodata_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0 HC HJ HR)].
split; [|split; [exact OK | exact PO]].
apply (afn_pre_at tfibsegs B STK_fuzz_strdup (spZ regs) FS_PSTAT_FP ly S W (unpoison Up mem) md [] lyc Sc Wc
  (unpoison Up memM) mdM k regsM STK_fuzz_malloc (-32) [] HJ);
  first [ solve [lia]
        | solve [rewrite R1; apply ret_ok_even; rewrite unsigned_lit_small by (unfold RA_SD_MALLOC; lia); reflexivity]
        | solve [unfold raZ; rewrite R1, unsigned_lit_small by (unfold RA_SD_MALLOC; lia); unfold RA_SD_MALLOC; lia]
        | solve [exact R3] | solve [exact R4] | solve [apply achain_low; exact Hs0] ].
Qed.

(* ---- the strlen call at 0x82cfc: astrlen_realizesU's premises from the caller's journal ---- *)
(* the read-only view and fs_img_facts read on the unpoisoned memory: read-only bytes are below the shadow *)
Lemma sd_arodata_unpoison : forall ly S Up (W : world tfibsegs) m md, ARU tfibsegs B ly S Up W m md ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) m) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (unpoison Up m)).
Proof.
intros ly S Up W m md H HR a Hro Ho He.
pose proof (fsk_segs_img a (sd_ro_img a Hro)) as Hl. unfold FS_IMG_END in Hl.
rewrite (aview_at tfibsegs (w_H W) (unpoison Up m) m a); [exact (HR a Hro Ho He)|].
apply (unpoison_app B ly S Up W m md a H); unfold SHADOW_OFF; lia.
Qed.
Lemma sd_rom_view : forall ly S Up (W : world tfibsegs) m md, fs_img_facts tfibsegs B -> ARU tfibsegs B ly S Up W m md ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) m) -> rom_view tfibsegs W m.
Proof.
intros ly S Up W m md IMG H HR a Hrom.
pose proof H as (HAR & _ & _).
destruct (proj2 IMG ly S W (unpoison Up m) md HAR (sd_arodata_unpoison ly S Up W m md H HR)) as (Hrv & _).
destruct Hrom as (sg & Hsg & Hw & Hr).
pose proof (fsk_segs_img a (ex_intro _ sg (conj Hsg Hr))) as Hl. unfold FS_IMG_END in Hl.
rewrite <- (aview_at tfibsegs (w_H W) (unpoison Up m) m a (unpoison_app B ly S Up W m md a H ltac:(lia)
  ltac:(left; unfold SHADOW_OFF; lia))).
apply Hrv. exists sg. split; [exact Hsg | split; [exact Hw | exact Hr]].
Qed.
Lemma sd_strlen_pre : forall ly S Up W regs mem md lyc Sc Wc regsT memT mdT k,
  ARU tfibsegs B lyc Sc Up Wc memT mdT ->
  ajournal tfibsegs B STK_fuzz_strdup (spZ regs) FS_PSTAT_FP ly S W (unpoison Up mem) md [] lyc Sc Wc
    (unpoison Up memT) mdT k ->
  spZ regsT = spZ regs - 32 -> YK0s.ret_ok (YK11.getr regsT 1) ->
  YK11.getr regsT 3 = w64 (as_gp B) -> YK11.getr regsT 4 = w64 (as_tp B) ->
  ecall_preU_k tfibsegs B STK_RT_STR lyc Sc Up Wc regsT memT mdT.
Proof.
intros ly S Up W regs mem md lyc Sc Wc regsT memT mdT k HC HJ Esp Hra R3 R4.
pose proof HC as (_ & OK & PO).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof asan_consts as (C1 & _ & C3 & _).
assert (FS : STK_fuzz_strdup = 16448) by reflexivity. assert (FR : STK_RT_STR = 8192) by reflexivity.
assert (ESTACK = 4096) as Hes by reflexivity.
split; [split; [|split; [exact OK | exact PO]]|].
- apply (ecall_pre_at tfibsegs B STK_fuzz_strdup (spZ regs) FS_PSTAT_FP ly S W (unpoison Up mem) md [] lyc Sc Wc
    (unpoison Up memT) mdT k regsT (-32) HJ);
    first [solve [exact Hra] | solve [exact R3] | solve [exact R4]
          | lazymatch goal with |- _ mod _ = _ => solve [reflexivity] end | solve [lia]].
- split; [rewrite Eslo; lia|].
  intros a Ha. apply (fsw_apresent_unpoison B lyc Sc Up Wc memT mdT a HC); first [solve [lia] | solve [apply Hpres; lia]].
Qed.

(* ---- the frame: the four saved registers read back from the symbolic state, and as the resumed states' chunks ---- *)
Definition sd_frame_vals (m : word -> option byte) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
  val_mem tfibsegs m (sp0 - 8) 8 (raZ regs) /\ val_mem tfibsegs m (sp0 - 16) 8 (s0Z regs) /\
  val_mem tfibsegs m (sp0 - 24) 8 (bv_unsigned (YK11.getr regs 9)) /\
  val_mem tfibsegs m (sp0 - 32) 8 (bv_unsigned (YK11.getr regs 18)).
Definition sd_entry_region : YP09.region :=
  YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0
    [YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
     YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
Lemma sd_entry_region_eq : ss_mem (fst (sym_runN tfibsegs sd_tbl FUEL (fss0 A_fuzz_strdup 32))) = [sd_entry_region].
Proof. vm_compute. reflexivity. Qed.
(* after the entry run: the frame holds the entry ra, s0, s1, s2 *)
Lemma sd_vals_entry : forall regs (H : word -> bool) ss ms,
  st_ok tfibsegs (Ereg regs []) ss (restrict H ms) -> ss_mem ss = [sd_entry_region] ->
  sd_frame_vals (mrestrict H (ms_mem ms)) (spZ regs) regs.
Proof.
intros regs H ss ms HS Hm.
pose proof (fsw_region_nth (Ereg regs []) ss (restrict H ms) 0 sd_entry_region HS ltac:(rewrite Hm; reflexivity)) as HR.
cbn [ms_mem restrict] in HR.
assert (E2 : bv_unsigned (ew (Ereg regs []) 2) = spZ regs) by (rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
assert (F : forall (n : nat) (r : bv 5) od, Z.of_nat n = bv_unsigned r -> In (YP09.mkChunk od (CVal 8 (SOff n 0))) (YP09.r_chunks sd_entry_region) ->
  val_mem tfibsegs (mrestrict H (ms_mem ms)) (spZ regs + od) 8 (bv_unsigned (YK11.getr regs r))).
{ intros n r od Hn Hin. apply (fsw_field (Ereg regs []) _ 2 (spZ regs) _ (-32) 0 (-32) 0 od 8%N (SOff n 0) _ HR E2 Hin);
    first [ solve [apply u64_range]
          | lazymatch goal with |- sv_denot _ _ = _ =>
              rewrite fsw_SOff0, (ew_Ereg_nat regs [] n r Hn); symmetry; apply Z_to_bv_bv_unsigned end
          | solve [cbn; lia] ]. }
split; [|split; [|split]].
- replace (spZ regs - 8) with (spZ regs + -8) by lia. exact (F 1%nat 1%bv (-8) eq_refl ltac:(cbn; tauto)).
- replace (spZ regs - 16) with (spZ regs + -16) by lia. exact (F 8%nat 8%bv (-16) eq_refl ltac:(cbn; tauto)).
- replace (spZ regs - 24) with (spZ regs + -24) by lia. exact (F 9%nat 9%bv (-24) eq_refl ltac:(cbn; tauto)).
- replace (spZ regs - 32) with (spZ regs + -32) by lia. exact (F 18%nat 18%bv (-32) eq_refl ltac:(cbn; tauto)).
Qed.
(* after a run resumed with fss_ret over sd_cs: the frame still holds them *)
Lemma sd_vals_ret : forall regs regsR (H : word -> bool) ss ms,
  st_ok tfibsegs (Ereg regsR (sd_extra regs)) ss (restrict H ms) -> ss_mem ss = [fstk_ret 32 sd_cs] ->
  spZ regsR = spZ regs - 32 ->
  sd_frame_vals (mrestrict H (ms_mem ms)) (spZ regs) regs.
Proof.
intros regs regsR H ss ms HS Hm Esp.
pose proof (fsw_region_nth (Ereg regsR (sd_extra regs)) ss (restrict H ms) 0 (fstk_ret 32 sd_cs) HS ltac:(rewrite Hm; reflexivity)) as HR.
cbn [ms_mem restrict] in HR. unfold fstk_ret in HR.
assert (E2 : bv_unsigned (ew (Ereg regsR (sd_extra regs)) 2) = spZ regs - 32)
  by (rewrite (ew_Ereg_nat regsR _ 2 2%bv eq_refl); exact Esp).
assert (F : forall (j : nat) (r : bv 5) od, nth j (sd_extra regs) (Z_to_bv 64 0) = YK11.getr regs r ->
  In (YP09.mkChunk od (CVal 8 (SOff (32 + j) 0))) sd_cs ->
  val_mem tfibsegs (mrestrict H (ms_mem ms)) (spZ regs - 32 + od) 8 (bv_unsigned (YK11.getr regs r))).
{ intros j r od Hj Hin. apply (fsw_field (Ereg regsR (sd_extra regs)) _ 2 (spZ regs - 32) _ 0 32 0 32 od 8%N (SOff (32 + j) 0) _ HR E2 Hin);
    first [ solve [apply u64_range]
          | lazymatch goal with |- sv_denot _ _ = _ =>
              rewrite fsw_SOff0, ew_Ereg_extra, Hj; symmetry; apply Z_to_bv_bv_unsigned end
          | solve [cbn; lia] ]. }
split; [|split; [|split]].
- replace (spZ regs - 8) with (spZ regs - 32 + 24) by lia. exact (F 0%nat 1%bv 24 eq_refl ltac:(cbn; tauto)).
- replace (spZ regs - 16) with (spZ regs - 32 + 16) by lia. exact (F 1%nat 8%bv 16 eq_refl ltac:(cbn; tauto)).
- replace (spZ regs - 24) with (spZ regs - 32 + 8) by lia. exact (F 2%nat 9%bv 8 eq_refl ltac:(cbn; tauto)).
- replace (spZ regs - 32) with (spZ regs - 32 + 0) at 1 by lia. exact (F 3%nat 18%bv 0 eq_refl ltac:(cbn; tauto)).
Qed.
(* the four values as the resumed state's chunks (FSW_K fsw_after_callU's Forall chunk_ok premise) *)
Lemma sd_chunks_of_vals : forall regs regs' m sp0,
  sd_frame_vals m sp0 regs -> Forall (YP09.chunk_ok tfibsegs (Ereg regs' (sd_extra regs)) m (sp0 - 32)) sd_cs.
Proof.
intros regs regs' m sp0 (V1 & V2 & V3 & V4).
assert (F : forall (j : nat) (r : bv 5) od, nth j (sd_extra regs) (Z_to_bv 64 0) = YK11.getr regs r ->
  val_mem tfibsegs m (sp0 - 32 + od) 8 (bv_unsigned (YK11.getr regs r)) ->
  YP09.chunk_ok tfibsegs (Ereg regs' (sd_extra regs)) m (sp0 - 32) (YP09.mkChunk od (CVal 8 (SOff (32 + j) 0)))).
{ intros j r od Hj Hv. apply (chunk_ok_val tfibsegs _ _ _ od 8%N (SOff (32 + j) 0) (bv_unsigned (YK11.getr regs r)));
    first [ solve [exact Hv] | solve [apply u64_range]
          | lazymatch goal with |- sv_denot _ _ = _ =>
              rewrite fsw_SOff0, ew_Ereg_extra, Hj; symmetry; apply Z_to_bv_bv_unsigned end
          | solve [cbn; lia] ]. }
unfold sd_cs. repeat constructor.
- apply (F 0%nat 1%bv 24 eq_refl). replace (sp0 - 32 + 24) with (sp0 - 8) by lia. exact V1.
- apply (F 1%nat 8%bv 16 eq_refl). replace (sp0 - 32 + 16) with (sp0 - 16) by lia. exact V2.
- apply (F 2%nat 9%bv 8 eq_refl). replace (sp0 - 32 + 8) with (sp0 - 24) by lia. exact V3.
- apply (F 3%nat 18%bv 0 eq_refl). replace (sp0 - 32 + 0) with (sp0 - 32) by lia. exact V4.
Qed.

(* ---- the entry segment: prologue, s0 := s, up to the strlen call at 0x82cfc (FSW_K U-form run step) ---- *)
Definition sd_ssT : sstate := Eval vm_compute in fst (sym_runN tfibsegs sd_tbl FUEL (fss0 A_fuzz_strdup 32)).
Lemma sd_ssT_eq : fst (sym_runN tfibsegs sd_tbl FUEL (fss0 A_fuzz_strdup 32)) = sd_ssT.
Proof. vm_compute. reflexivity. Qed.
Lemma sd_to_strlen : forall ly S Up W regs mem md ch (Q : world tfibsegs -> config -> Prop),
  fpreU tfibsegs B STK_fuzz_strdup ly S Up W regs mem md ch ->
  (forall ms mat,
     st_ok tfibsegs (Ereg regs []) sd_ssT (restrict (w_H W) ms) ->
     ajournal tfibsegs B STK_fuzz_strdup (spZ regs) FS_PSTAT_FP ly S W (unpoison Up mem) md [] ly S W
       (unpoison Up (ms_mem ms)) (with_vm_backing (m_vm_lazy md) mat md) 0 ->
     ARU tfibsegs B ly S Up W (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md) ->
     same_below mem (ms_mem ms) alloc_ceiling ->
     sd_frame_vals (mrestrict (w_H W) (ms_mem ms)) (spZ regs) regs ->
     ms = YK11.mkst (ms_regs ms) (Z_to_bv 64 PC_strlen) (ms_mem ms) (YK11.seg_rom tfibsegs) ->
     YK11.getr (ms_regs ms) 1 = Z_to_bv 64 RA_SD_STRLEN -> spZ (ms_regs ms) = spZ regs - 32 ->
     YK11.getr (ms_regs ms) 8 = YK11.getr regs 10 -> YK11.getr (ms_regs ms) 10 = YK11.getr regs 10 ->
     YK11.getr (ms_regs ms) 3 = YK11.getr regs 3 -> YK11.getr (ms_regs ms) 4 = YK11.getr regs 4 ->
     (forall r, acallee_saved r -> r <> 2 -> r <> 8 -> YK11.getr (ms_regs ms) (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
     SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  SRr tfibsegs W (cfg_at tfibsegs A_fuzz_strdup regs mem md) Q.
Proof.
intros ly S Up W regs mem md ch Q HPRE K.
pose proof HPRE as ((HAP & OK & PO) & HRO).
pose proof (fsw_ARU B STK_fuzz_strdup ly S Up W regs mem md ch (proj1 HPRE)) as HARU.
pose proof (fsw_sp B STK_fuzz_strdup ly S Up W regs mem md ch (proj1 HPRE)) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _). assert (FS : STK_fuzz_strdup = 16448) by reflexivity.
pose proof (fsw_entry B STK_fuzz_strdup 32 ly S Up W regs mem md ch A_fuzz_strdup (proj1 HPRE) ltac:(lia)
  ltac:(vm_compute; reflexivity)) as HS.
pose proof (ajournal_init tfibsegs B STK_fuzz_strdup FS_PSTAT_FP ly S W regs (unpoison Up mem) md ch HAP) as HJ.
assert (E2 : bv_unsigned (ew (Ereg regs []) 2) = spZ regs) by (rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
unfold cfg_at. change (w64 A_fuzz_strdup) with (Z_to_bv 64 A_fuzz_strdup).
fsw_aj_runU sd_tbl_ok HS HJ HARU.
all: first [ solve [ unfold fss0; cbn [ss_mem]; eapply awr_ok_cons_stack with (n := 2%nat); first [solve [reflexivity] | solve [exact E2] | solve [cbn; lia] | solve [apply awr_ok_nil]] ] | idtac ].
assert (SB : same_below mem (ms_mem ms) alloc_ceiling).
{ unfold fss0 in HF. cbn [ss_mem] in HF.
  apply (same_below_frame1 _ (fstk 32) mem (ms_mem ms) alloc_ceiling HF); first [solve [lia] | idtac].
  cbn [fstk YP09.r_base YP09.r_wlo base_val]. rewrite E2. lia. }
change (st_ok tfibsegs (Ereg regs []) sd_ssT (restrict (w_H W) ms)) in HS.
set (E := Ereg regs []) in *.
assert (Rg : forall (r : bv 5) n, sr_get (ss_regs sd_ssT) r = SOff n 0 -> forall r', Z.of_nat n = bv_unsigned r' ->
  YK11.getr (ms_regs ms) r = YK11.getr regs r') by (intros r n Hr r' Hn; exact (fsw_reg_atom _ regs [] _ ms r r' n HS Hr Hn)).
apply K.
- exact HS.
- exact HJ.
- exact HARU.
- exact SB.
- apply (sd_vals_entry regs (w_H W) sd_ssT ms HS). vm_compute. reflexivity.
- exact (st_ok_restrict_mkst tfibsegs (w_H W) E sd_ssT ms HS eq_refl).
- exact (fsw_reg_lit _ E _ ms 1%bv RA_SD_STRLEN HS ltac:(vm_compute; reflexivity) ltac:(unfold RA_SD_STRLEN; lia)).
- unfold spZ at 1. exact (fsw_reg_off _ E _ ms 2%bv 2 (-32) (spZ regs) HS ltac:(vm_compute; reflexivity) E2 ltac:(lia)).
- exact (Rg 8%bv 10%nat ltac:(vm_compute; reflexivity) 10%bv eq_refl).
- exact (Rg 10%bv 10%nat ltac:(vm_compute; reflexivity) 10%bv eq_refl).
- exact (Rg 3%bv 3%nat ltac:(vm_compute; reflexivity) 3%bv eq_refl).
- exact (Rg 4%bv 4%nat ltac:(vm_compute; reflexivity) 4%bv eq_refl).
- intros r Hr H2 H8. unfold acallee_saved in Hr.
  assert (Rz : forall z, 0 <= z < 32 -> sr_get (ss_regs sd_ssT) (Z_to_bv 5 z) = SOff (Z.to_nat z) 0 ->
    YK11.getr (ms_regs ms) (Z_to_bv 5 z) = YK11.getr regs (Z_to_bv 5 z)).
  { intros z Hz Hs. apply (Rg _ (Z.to_nat z) Hs). rewrite Z_to_bv_unsigned, bv_wrap_small; [lia|].
    change (bv_modulus 5) with 32. lia. }
  assert (Hc : r = 3 \/ r = 4 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/
    r = 26 \/ r = 27) by lia.
  apply Rz; [lia|].
  repeat (destruct Hc as [->|Hc]; [vm_compute; reflexivity|]); subst r; vm_compute; reflexivity.
Qed.

(* a callee-saved register read back after a run from a resumed state whose symbolic value is its own atom *)
Lemma sd_kept_after_run : forall regsR extra ss ms (H : word -> bool),
  st_ok tfibsegs (Ereg regsR extra) ss (restrict H ms) ->
  forall z, 0 <= z < 32 -> sr_get (ss_regs ss) (Z_to_bv 5 z) = SOff (Z.to_nat z) 0 ->
  YK11.getr (ms_regs ms) (Z_to_bv 5 z) = YK11.getr regsR (Z_to_bv 5 z).
Proof.
intros regsR extra ss ms H HS z Hz Hs. apply (fsw_reg_atom H regsR extra ss ms _ _ (Z.to_nat z) HS Hs).
rewrite Z_to_bv_unsigned, bv_wrap_small; [lia|]. change (bv_modulus 5) with 32. lia.
Qed.

(* ---- after strlen: s1 := a0 + 1; a0 := s1; up to the fuzz_malloc call at 0x82d08 ---- *)
Definition sd_ssM : sstate := Eval vm_compute in fst (sym_runN tfibsegs sd_tbl FUEL (fss_ret RA_SD_STRLEN 32 sd_cs)).
Lemma sd_to_malloc : forall regs ly S Up W memE mdE lyc Sc Wc regs1 mem1 md1 k (Q : world tfibsegs -> config -> Prop),
  st_ok tfibsegs (Ereg regs1 (sd_extra regs)) (fss_ret RA_SD_STRLEN 32 sd_cs)
    (restrict (w_H Wc) (YK11.mkst regs1 (Z_to_bv 64 RA_SD_STRLEN) mem1 (YK11.seg_rom tfibsegs))) ->
  ARU tfibsegs B lyc Sc Up Wc mem1 md1 ->
  ajournal tfibsegs B STK_fuzz_strdup (spZ regs) FS_PSTAT_FP ly S W (unpoison Up memE) mdE [] lyc Sc Wc
    (unpoison Up mem1) md1 k ->
  spZ regs1 = spZ regs - 32 -> bv_unsigned (YK11.getr regs1 10) + 1 < 2 ^ 64 ->
  (forall ms mat,
     st_ok tfibsegs (Ereg regs1 (sd_extra regs)) sd_ssM (restrict (w_H Wc) ms) ->
     ajournal tfibsegs B STK_fuzz_strdup (spZ regs) FS_PSTAT_FP ly S W (unpoison Up memE) mdE [] lyc Sc Wc
       (unpoison Up (ms_mem ms)) (with_vm_backing (m_vm_lazy md1) mat md1) k ->
     ARU tfibsegs B lyc Sc Up Wc (ms_mem ms) (with_vm_backing (m_vm_lazy md1) mat md1) ->
     same_below mem1 (ms_mem ms) alloc_ceiling ->
     sd_frame_vals (mrestrict (w_H Wc) (ms_mem ms)) (spZ regs) regs ->
     ms = YK11.mkst (ms_regs ms) (Z_to_bv 64 A_fuzz_malloc) (ms_mem ms) (YK11.seg_rom tfibsegs) ->
     YK11.getr (ms_regs ms) 1 = Z_to_bv 64 RA_SD_MALLOC -> spZ (ms_regs ms) = spZ regs - 32 ->
     bv_unsigned (YK11.getr (ms_regs ms) 10) = bv_unsigned (YK11.getr regs1 10) + 1 ->
     bv_unsigned (YK11.getr (ms_regs ms) 9) = bv_unsigned (YK11.getr regs1 10) + 1 ->
     (forall z, 0 < z < 32 -> z <> 1 -> z <> 9 -> z <> 10 ->
        YK11.getr (ms_regs ms) (Z_to_bv 5 z) = YK11.getr regs1 (Z_to_bv 5 z)) ->
     SRr tfibsegs Wc (mkCfg ms (with_vm_backing (m_vm_lazy md1) mat md1)) Q) ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regs1 (Z_to_bv 64 RA_SD_STRLEN) mem1 (YK11.seg_rom tfibsegs)) md1) Q.
Proof.
intros regs ly S Up W memE mdE lyc Sc Wc regs1 mem1 md1 k Q HS HARU HJ Esp H64 K.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & _). assert (FS : STK_fuzz_strdup = 16448) by reflexivity.
assert (E2 : bv_unsigned (ew (Ereg regs1 (sd_extra regs)) 2) = spZ regs - 32)
  by (rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl); exact Esp).
assert (E10 : bv_unsigned (ew (Ereg regs1 (sd_extra regs)) 10) = bv_unsigned (YK11.getr regs1 10))
  by (rewrite (ew_Ereg_nat regs1 _ 10 10%bv eq_refl); reflexivity).
fsw_aj_runU sd_tbl_ok HS HJ HARU.
all: first [ solve [ fsw_awr_ret E2 32 ] | idtac ].
assert (SB : same_below mem1 (ms_mem ms) alloc_ceiling).
{ unfold fss_ret in HF. cbn [ss_mem] in HF.
  apply (same_below_frame1 _ (fstk_ret 32 sd_cs) mem1 (ms_mem ms) alloc_ceiling HF); first [solve [lia] | idtac].
  cbn [fstk_ret YP09.r_base YP09.r_wlo base_val]. rewrite E2. lia. }
change (st_ok tfibsegs (Ereg regs1 (sd_extra regs)) sd_ssM (restrict (w_H Wc) ms)) in HS.
apply K.
- exact HS.
- exact HJ.
- exact HARU.
- exact SB.
- apply (sd_vals_ret regs regs1 (w_H Wc) sd_ssM ms HS); [vm_compute; reflexivity | exact Esp].
- exact (st_ok_restrict_mkst tfibsegs (w_H Wc) _ sd_ssM ms HS eq_refl).
- exact (fsw_reg_lit _ _ _ ms 1%bv RA_SD_MALLOC HS ltac:(vm_compute; reflexivity) ltac:(unfold RA_SD_MALLOC; lia)).
- unfold spZ at 1. exact (fsw_reg_off _ _ _ ms 2%bv 2 0 (spZ regs - 32) HS ltac:(vm_compute; reflexivity) E2 ltac:(lia)) ||
  (rewrite (fsw_reg_off _ _ _ ms 2%bv 2 0 (spZ regs - 32) HS ltac:(vm_compute; reflexivity) E2 ltac:(lia)); lia).
- exact (fsw_reg_off _ _ _ ms 10%bv 10 1 _ HS ltac:(vm_compute; reflexivity) E10 ltac:(pose proof (u64_range (YK11.getr regs1 10)); lia)).
- exact (fsw_reg_off _ _ _ ms 9%bv 10 1 _ HS ltac:(vm_compute; reflexivity) E10 ltac:(pose proof (u64_range (YK11.getr regs1 10)); lia)).
- intros z Hz H1 H9 H10. apply (sd_kept_after_run regs1 (sd_extra regs) sd_ssM ms (w_H Wc) HS z ltac:(lia)).
  assert (Hc : z = 2 \/ z = 3 \/ z = 4 \/ z = 5 \/ z = 6 \/ z = 7 \/ z = 8 \/ z = 11 \/ z = 12 \/ z = 13 \/ z = 14 \/ z = 15 \/
    z = 16 \/ z = 17 \/ z = 18 \/ z = 19 \/ z = 20 \/ z = 21 \/ z = 22 \/ z = 23 \/ z = 24 \/ z = 25 \/ z = 26 \/ z = 27 \/
    z = 28 \/ z = 29 \/ z = 30 \/ z = 31) by lia.
  repeat (destruct Hc as [->|Hc]; [vm_compute; reflexivity|]); subst z; vm_compute; reflexivity.
Qed.

(* ---- after fuzz_malloc, a0 <> 0: s2 := a0; `beqz a0` not taken; a0, a1, a2 := s2, s0, s1; up to the memcpy call ---- *)
Definition sd_ssB : sstate := Eval vm_compute in fst (sym_runN tfibsegs sd_tbl FUEL (fss_ret RA_SD_MALLOC 32 sd_cs)).
Definition sd_ssC : sstate := Eval vm_compute in
  fst (sym_runN tfibsegs sd_tbl FUEL (add_cond sd_ssB (mkAC BC_NE (SOff 10 0) (SLit 0)))).
Lemma sd_to_memcpy : forall regs ly S Up W memE mdE lyc Sc Uc Wc regs2 mem2 md2 k (Q : world tfibsegs -> config -> Prop),
  st_ok tfibsegs (Ereg regs2 (sd_extra regs)) (fss_ret RA_SD_MALLOC 32 sd_cs)
    (restrict (w_H Wc) (YK11.mkst regs2 (Z_to_bv 64 RA_SD_MALLOC) mem2 (YK11.seg_rom tfibsegs))) ->
  ARU tfibsegs B lyc Sc Uc Wc mem2 md2 ->
  ajournal tfibsegs B STK_fuzz_strdup (spZ regs) FS_PSTAT_FP ly S W (unpoison Up memE) mdE [] lyc Sc Wc
    (unpoison Uc mem2) md2 k ->
  spZ regs2 = spZ regs - 32 -> YK11.getr regs2 10 <> w64 0 ->
  (forall ms mat,
     st_ok tfibsegs (Ereg regs2 (sd_extra regs)) sd_ssC (restrict (w_H Wc) ms) ->
     ajournal tfibsegs B STK_fuzz_strdup (spZ regs) FS_PSTAT_FP ly S W (unpoison Up memE) mdE [] lyc Sc Wc
       (unpoison Uc (ms_mem ms)) (with_vm_backing (m_vm_lazy md2) mat md2) k ->
     ARU tfibsegs B lyc Sc Uc Wc (ms_mem ms) (with_vm_backing (m_vm_lazy md2) mat md2) ->
     same_below mem2 (ms_mem ms) alloc_ceiling ->
     sd_frame_vals (mrestrict (w_H Wc) (ms_mem ms)) (spZ regs) regs ->
     ms = YK11.mkst (ms_regs ms) (Z_to_bv 64 PC_memcpy) (ms_mem ms) (YK11.seg_rom tfibsegs) ->
     YK11.getr (ms_regs ms) 1 = Z_to_bv 64 RA_SD_MEMCPY -> spZ (ms_regs ms) = spZ regs - 32 ->
     YK11.getr (ms_regs ms) 10 = YK11.getr regs2 10 -> YK11.getr (ms_regs ms) 11 = YK11.getr regs2 8 ->
     YK11.getr (ms_regs ms) 12 = YK11.getr regs2 9 -> YK11.getr (ms_regs ms) 18 = YK11.getr regs2 10 ->
     (forall z, 0 < z < 32 -> z <> 1 -> z <> 11 -> z <> 12 -> z <> 18 ->
        YK11.getr (ms_regs ms) (Z_to_bv 5 z) = YK11.getr regs2 (Z_to_bv 5 z)) ->
     SRr tfibsegs Wc (mkCfg ms (with_vm_backing (m_vm_lazy md2) mat md2)) Q) ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regs2 (Z_to_bv 64 RA_SD_MALLOC) mem2 (YK11.seg_rom tfibsegs)) md2) Q.
Proof.
intros regs ly S Up W memE mdE lyc Sc Uc Wc regs2 mem2 md2 k Q HS HARU HJ Esp H0 K.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & _). assert (FS : STK_fuzz_strdup = 16448) by reflexivity.
set (E := Ereg regs2 (sd_extra regs)) in *.
assert (E2 : bv_unsigned (ew E 2) = spZ regs - 32) by (unfold E; rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl); exact Esp).
assert (U10 : U E (SOff 10 0) = bv_unsigned (YK11.getr regs2 10))
  by (apply U_atom; [unfold E; rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned
                    | apply u64_range]).
assert (UZ : U E (SLit 0) = 0) by (apply U_lit; lia).
fsw_aj_runU sd_tbl_ok HS HJ HARU.
all: first [ solve [ fsw_awr_ret E2 32 ] | idtac ].
assert (SB1 : same_below mem2 (ms_mem ms) alloc_ceiling).
{ unfold fss_ret in HF. cbn [ss_mem] in HF.
  apply (same_below_frame1 _ (fstk_ret 32 sd_cs) mem2 (ms_mem ms) alloc_ceiling HF); first [solve [lia] | idtac].
  cbn [fstk_ret YP09.r_base YP09.r_wlo base_val]. rewrite E2. lia. }
change (st_ok tfibsegs E sd_ssB (restrict (w_H Wc) ms)) in HS.
eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 10 0) (b := SLit 0) (1 := HS).
(* the two branch continuations of SRr_sym_branch: taken (a0 = 0) refuted, then not taken (the copy arm) *)
2: intros Hb HS3.
1: { intros Hb _. exfalso. rewrite branch_eq_U, U10, UZ in Hb. apply Z.eqb_eq in Hb. apply H0.
     unfold w64. rewrite <- Hb. symmetry. apply Z_to_bv_bv_unsigned. }
clear HS. cbn [neg_bc] in HS3. rename ms into msB. clear HF HFr HG.
fsw_aj_runU sd_tbl_ok HS3 HJ HARU.
all: first [ solve [ cbn [add_cond ss_mem sd_ssB]; eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -32); first [solve [reflexivity] | solve [exact E2] | solve [cbn; lia] | solve [apply awr_ok_nil]] ] | idtac ].
assert (SB2 : same_below (ms_mem msB) (ms_mem ms) alloc_ceiling).
{ cbn [add_cond ss_mem sd_ssB] in HF.
  apply (same_below_frame1 _ (fstk_ret 32 sd_cs) (ms_mem msB) (ms_mem ms) alloc_ceiling HF); first [solve [lia] | idtac].
  cbn [fstk_ret YP09.r_base YP09.r_wlo base_val]. rewrite E2. lia. }
change (st_ok tfibsegs E sd_ssC (restrict (w_H Wc) ms)) in HS3.
assert (Rg : forall z, 0 < z < 32 -> sr_get (ss_regs sd_ssC) (Z_to_bv 5 z) = SOff (Z.to_nat z) 0 ->
  YK11.getr (ms_regs ms) (Z_to_bv 5 z) = YK11.getr regs2 (Z_to_bv 5 z))
  by (intros z Hz Hs; exact (sd_kept_after_run regs2 (sd_extra regs) sd_ssC ms (w_H Wc) HS3 z ltac:(lia) Hs)).
apply K.
- exact HS3.
- exact HJ.
- exact HARU.
- exact (same_below_trans _ _ _ _ SB1 SB2).
- apply (sd_vals_ret regs regs2 (w_H Wc) sd_ssC ms HS3); [vm_compute; reflexivity | exact Esp].
- exact (st_ok_restrict_mkst tfibsegs (w_H Wc) E sd_ssC ms HS3 eq_refl).
- exact (fsw_reg_lit _ E _ ms 1%bv RA_SD_MEMCPY HS3 ltac:(vm_compute; reflexivity) ltac:(unfold RA_SD_MEMCPY; lia)).
- unfold spZ at 1. rewrite (fsw_reg_off _ E _ ms 2%bv 2 0 (spZ regs - 32) HS3 ltac:(vm_compute; reflexivity) E2 ltac:(lia)). lia.
- exact (fsw_reg_atom _ regs2 _ _ ms 10%bv 10%bv 10 HS3 ltac:(vm_compute; reflexivity) eq_refl).
- exact (fsw_reg_atom _ regs2 _ _ ms 11%bv 8%bv 8 HS3 ltac:(vm_compute; reflexivity) eq_refl).
- exact (fsw_reg_atom _ regs2 _ _ ms 12%bv 9%bv 9 HS3 ltac:(vm_compute; reflexivity) eq_refl).
- exact (fsw_reg_atom _ regs2 _ _ ms 18%bv 10%bv 10 HS3 ltac:(vm_compute; reflexivity) eq_refl).
- intros z Hz H1 H11 H12 H18. apply Rg; [lia|].
  assert (Hc : z = 2 \/ z = 3 \/ z = 4 \/ z = 5 \/ z = 6 \/ z = 7 \/ z = 8 \/ z = 9 \/ z = 10 \/ z = 13 \/ z = 14 \/ z = 15 \/
    z = 16 \/ z = 17 \/ z = 19 \/ z = 20 \/ z = 21 \/ z = 22 \/ z = 23 \/ z = 24 \/ z = 25 \/ z = 26 \/ z = 27 \/
    z = 28 \/ z = 29 \/ z = 30 \/ z = 31) by lia.
  repeat (destruct Hc as [->|Hc]; [vm_compute; reflexivity|]); subst z; vm_compute; reflexivity.
Qed.

(* the frame's four values survive a callee whose writes miss [sp0 - 32, sp0) *)
Lemma sd_frame_vals_kept : forall (H : word -> bool) m m' sp0 regs,
  (forall a, sp0 - 32 <= a < sp0 -> aview tfibsegs H m' a = aview tfibsegs H m a) ->
  sd_frame_vals (mrestrict H m) sp0 regs -> sd_frame_vals (mrestrict H m') sp0 regs.
Proof.
intros H m m' sp0 regs Hk (V1 & V2 & V3 & V4).
split; [|split; [|split]]; (eapply (val_mem_kept tfibsegs H H m m'); first [solve [eassumption] | idtac]);
  intros j Hj; apply Hk; lia.
Qed.
(* a runtime post in rt_post_roU form (strlen) read in fsw_intrin_atU's ARU-post form: same U, the write window Wr :=
   the callee's scratch window, the frame moved to the unpoisoned views; upoison_ok is the caller's (it reads only ly, S, U) *)
Lemma sd_unpoison_frame : forall (Uc : list (Z * Z)) (W : world tfibsegs) m m' (X : Z -> Prop),
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ X a ->
  aview tfibsegs (w_H W) (unpoison Uc m') a = aview tfibsegs (w_H W) (unpoison Uc m) a.
Proof.
intros Uc W m m' X Hfr a Ha Hx. destruct (in_ush Uc (bv_unsigned (Z_to_bv 64 a))) eqn:E.
- apply (aview_unpoison_in tfibsegs). exact E.
- rewrite !(aview_unpoison_out tfibsegs) by exact E. exact (Hfr a Ha Hx).
Qed.
Lemma sd_unpoison_present : forall (Uc : list (Z * Z)) (H : word -> bool) m m',
  (forall a, apresent H m a -> apresent H m' a) ->
  forall a, apresent H (unpoison Uc m) a -> apresent H (unpoison Uc m') a.
Proof.
intros Uc H m m' Hg a (Hh & b & Hb). split; [exact Hh|]. unfold unpoison in Hb |- *.
destruct (in_ush Uc (bv_unsigned (Z_to_bv 64 a))); [eexists; reflexivity|].
destruct (Hg a (conj Hh (ex_intro _ b Hb))) as (_ & b' & Hb'). exists b'. exact Hb'.
Qed.
Lemma sd_rt_ro_to_aru : forall K lyc Sc Uc (W : world tfibsegs) regsT memT mdT (R : Z -> Prop) W' c',
  upoison_ok B lyc Sc Uc ->
  rt_post_roU tfibsegs B K lyc Sc Uc W regsT memT mdT R W' c' ->
  W' = W /\ exists regs' mem' md',
    c' = mkCfg (YK11.mkst regs' (YK11.getr regsT 1) mem' (YK11.seg_rom tfibsegs)) md' /\
    ARU tfibsegs B lyc Sc Uc W mem' md' /\ same_but_materialized mdT md' /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - K <= a < spZ regsT) ->
       aview tfibsegs (w_H W) (unpoison Uc mem') a = aview tfibsegs (w_H W) (unpoison Uc memT) a) /\
    (forall a, apresent (w_H W) (unpoison Uc memT) a -> apresent (w_H W) (unpoison Uc mem') a) /\
    (aregs_preserved regsT regs' /\ (exists v, YK11.getr regs' 10 = w64 v /\ 0 <= v < 2 ^ 64 /\ R v) /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - K <= a < spZ regsT) ->
        aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) memT a)).
Proof.
intros K lyc Sc Uc W regsT memT mdT R W' c' OK
  (-> & regs' & mem' & md' & v & -> & HAR' & PO' & HP & Hsame & H10 & Hv & HR & Hfr & Hgr).
split; [reflexivity|]. exists regs', mem', md'.
split; [unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [split; [exact HAR' | split; [exact OK | exact PO']]|].
split; [exact Hsame|].
split; [exact (sd_unpoison_frame Uc W memT mem' (fun a => spZ regsT - K <= a < spZ regsT) Hfr)|].
split; [exact (sd_unpoison_present Uc (w_H W) memT mem' Hgr)|].
split; [exact HP|]. split; [exists v; split; [exact H10 | split; [exact Hv | exact HR]] | exact Hfr].
Qed.

(* ---- the strlen call (0x82cfc -> PC_strlen): astrlen_realizesU through FSW_K's fsw_intrin_atU, then the state resumed
   at 0x82d00 with a0 = length cs ---- *)
Lemma sd_strlen_step : forall ly S Up W regs mem md ms mdT s cs (Q : world tfibsegs -> config -> Prop),
  astrlen_realizesU tfibsegs B PC_strlen -> fs_img_facts tfibsegs B ->
  ARU tfibsegs B ly S Up W mem md -> arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem) ->
  ajournal tfibsegs B STK_fuzz_strdup (spZ regs) FS_PSTAT_FP ly S W (unpoison Up mem) md [] ly S W
    (unpoison Up (ms_mem ms)) mdT 0 ->
  ARU tfibsegs B ly S Up W (ms_mem ms) mdT ->
  same_below mem (ms_mem ms) alloc_ceiling ->
  sd_frame_vals (mrestrict (w_H W) (ms_mem ms)) (spZ regs) regs ->
  ms = YK11.mkst (ms_regs ms) (Z_to_bv 64 PC_strlen) (ms_mem ms) (YK11.seg_rom tfibsegs) ->
  YK11.getr (ms_regs ms) 1 = Z_to_bv 64 RA_SD_STRLEN -> spZ (ms_regs ms) = spZ regs - 32 ->
  YK11.getr (ms_regs ms) 10 = w64 s ->
  YK11.getr (ms_regs ms) 3 = w64 (as_gp B) -> YK11.getr (ms_regs ms) 4 = w64 (as_tp B) ->
  cstr_ok tfibsegs W mem s cs ->
  (forall regs1 mem1 md1,
     st_ok tfibsegs (Ereg regs1 (sd_extra regs)) (fss_ret RA_SD_STRLEN 32 sd_cs)
       (restrict (w_H W) (YK11.mkst regs1 (Z_to_bv 64 RA_SD_STRLEN) mem1 (YK11.seg_rom tfibsegs))) ->
     ajournal tfibsegs B STK_fuzz_strdup (spZ regs) FS_PSTAT_FP ly S W (unpoison Up mem) md [] ly S W
       (unpoison Up mem1) md1 0 ->
     ARU tfibsegs B ly S Up W mem1 md1 ->
     spZ regs1 = spZ regs - 32 -> YK11.getr regs1 10 = w64 (Z.of_nat (length cs)) ->
     aregs_preserved (ms_regs ms) regs1 ->
     (forall a, 0 <= a < alloc_ceiling -> aview tfibsegs (w_H W) mem1 a = aview tfibsegs (w_H W) (ms_mem ms) a) ->
     SRr tfibsegs W (mkCfg (YK11.mkst regs1 (Z_to_bv 64 RA_SD_STRLEN) mem1 (YK11.seg_rom tfibsegs)) md1) Q) ->
  SRr tfibsegs W (mkCfg ms mdT) Q.
Proof.
intros ly S Up W regs mem md ms mdT s cs Q STRLEN IMG H0 HR HJ HARU SB HV Hms R1 Rsp R10 R3 R4 Hc K.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & _). assert (FS : STK_fuzz_strdup = 16448) by reflexivity.
assert (FR : STK_RT_STR = 8192) by reflexivity.
pose proof HARU as (_ & OK & _).
assert (Hra : YK0s.ret_ok (YK11.getr (ms_regs ms) 1))
  by (rewrite R1; apply ret_ok_even; rewrite unsigned_lit_small by (unfold RA_SD_STRLEN; lia); reflexivity).
rewrite Hms. change (Z_to_bv 64 PC_strlen) with (w64 PC_strlen).
eapply SRr_bind.
{ apply (fsw_intrin_atU B STK_fuzz_strdup (spZ regs) FS_PSTAT_FP ly S W (unpoison Up mem) md [] ly S Up W (ms_mem ms)
    mdT 0 Up (fun a => spZ (ms_regs ms) - STK_RT_STR <= a < spZ (ms_regs ms)) (YK11.getr (ms_regs ms) 1)
    (cfg_at tfibsegs PC_strlen (ms_regs ms) (ms_mem ms) mdT)
    (fun regs' mem' md' => aregs_preserved (ms_regs ms) regs' /\
       (exists v, YK11.getr regs' 10 = w64 v /\ 0 <= v < 2 ^ 64 /\ v = Z.of_nat (length cs)) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (ms_regs ms) - STK_RT_STR <= a < spZ (ms_regs ms)) ->
          aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) (ms_mem ms) a)) HJ).
  - eapply SRr_mono.
    + apply (STRLEN ly S Up W (ms_regs ms) (ms_mem ms) mdT s cs).
      * exact (sd_strlen_pre ly S Up W regs mem md ly S W (ms_regs ms) (ms_mem ms) mdT 0 HARU HJ Rsp Hra R3 R4).
      * apply (sd_rom_view ly S Up W (ms_mem ms) mdT IMG HARU).
        exact (sd_arodata_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0 HARU HJ HR).
      * exact R10.
      * exact (cstr_ok_below W mem (ms_mem ms) s cs SB Hc).
    + intros W' c' _ Hpost. exact (sd_rt_ro_to_aru STK_RT_STR ly S Up W (ms_regs ms) (ms_mem ms) mdT _ W' c' OK Hpost).
  - (* the callee's scratch window: awr_byte's stack arm (inside awr_byte0 on the one-text core) *)
    intros a Ha. rewrite Rsp in Ha. first [solve [left; left; lia] | solve [left; lia]]. }
intros W2 c2 _ (-> & regs1 & mem1 & md1 & -> & HJ1 & HARU1 & (HP & (v & H10 & Hv & ->) & Hfr)).
assert (Usp : spZ regs1 = spZ regs - 32).
{ unfold spZ. rewrite (fsw_pres (ms_regs ms) regs1 2%bv HP ltac:(unfold acallee_saved; vm_compute; lia)). exact Rsp. }
rewrite R1.
apply K.
- apply (fsw_resume_after_rtU B STK_fuzz_strdup (spZ regs) FS_PSTAT_FP ly S W (unpoison Up mem) md [] ly S Up W mem1 md1 0
    (ms_regs ms) regs1 (ms_mem ms) 32 (sd_extra regs) sd_cs RA_SD_STRLEN HJ1 HARU1 HP Rsp ltac:(lia) ltac:(lia) eq_refl
    ltac:(vm_compute; reflexivity) ltac:(repeat constructor; cbn; lia) (sd_chunks_of_vals regs regs1 _ (spZ regs) HV)).
  intros a Ha. apply (mbyte_of_aview tfibsegs). apply Hfr; [lia | rewrite Rsp; lia].
- exact HJ1.
- exact HARU1.
- exact Usp.
- exact H10.
- exact HP.
- intros a Ha. apply Hfr; [lia | rewrite Rsp; lia].
Qed.

(* the block fuzz_malloc appended is not one of the blocks before (AR's pairwise disjoint blocks) *)
Lemma sd_new_not_old : forall ly S ly2 S2 W2 m2 md2 res nn,
  AR tfibsegs B ly2 S2 W2 m2 md2 -> ablocks B ly2 S2 = ablocks B ly S ++ [(res - HEAD, nn + HEAD)] -> 0 <= nn ->
  ~ In (res - HEAD, nn + HEAD) (ablocks B ly S).
Proof.
intros ly S ly2 S2 W2 m2 md2 res nn HAR Eab Hnn Hin. apply in_split in Hin as (l1 & l2 & El).
assert (E2 : ablocks B ly2 S2 = l1 ++ (res - HEAD, nn + HEAD) :: l2 ++ (res - HEAD, nn + HEAD) :: []).
{ rewrite Eab, El. rewrite <- app_assoc. reflexivity. }
pose proof (sep_blocks_pos tfibsegs B LAWS ly2 S2 W2 m2 md2 _ _ l1 l2 [] HAR E2) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. pose proof (req_size_pos (nn + HEAD) ltac:(unfold HEAD; lia)). lia.
Qed.

(* ---- the memcpy call (0x82d20 -> PC_memcpy) on the non-NULL arm: aintrin_realizesU OCpy through fsw_intrin_atU,
   the state resumed at 0x82d24, and the epilogue to fpostU with the arm-2 post ---- *)
Lemma sd_memcpy_step : forall ly S Up W regs mem md lyc Sc Wc ms mdC res cs live peak cnt fail,
  FSupoisonU.aintrin_realizesU tfibsegs B OCpy PC_memcpy ->
  ajournal tfibsegs B STK_fuzz_strdup (spZ regs) FS_PSTAT_FP ly S W (unpoison Up mem) md [] lyc Sc Wc
    (unpoison (Up ++ [(res - HEAD, HEAD)]) (ms_mem ms)) mdC 1 ->
  ARU tfibsegs B lyc Sc (Up ++ [(res - HEAD, HEAD)]) Wc (ms_mem ms) mdC ->
  sd_frame_vals (mrestrict (w_H Wc) (ms_mem ms)) (spZ regs) regs ->
  ms = YK11.mkst (ms_regs ms) (Z_to_bv 64 PC_memcpy) (ms_mem ms) (YK11.seg_rom tfibsegs) ->
  YK11.getr (ms_regs ms) 1 = Z_to_bv 64 RA_SD_MEMCPY -> spZ (ms_regs ms) = spZ regs - 32 ->
  YK11.getr (ms_regs ms) 3 = w64 (as_gp B) -> YK11.getr (ms_regs ms) 4 = w64 (as_tp B) ->
  YK11.getr (ms_regs ms) 10 = w64 res -> YK11.getr (ms_regs ms) 18 = w64 res ->
  YK11.getr (ms_regs ms) 12 = w64 (Z.of_nat (length cs) + 1) -> sd_kept regs (ms_regs ms) ->
  YK0s.ret_ok (YK11.getr regs 1) ->
  ablocks B lyc Sc = ablocks B ly S ++ [(res - HEAD, Z.of_nat (length cs) + 1 + HEAD)] ->
  fs_heads B lyc Sc (Up ++ [(res - HEAD, HEAD)]) -> 4096 + HEAD <= res ->
  fs_rblock tfibsegs B lyc Sc Wc (ms_mem ms) res (Z.of_nat (length cs) + 1) ->
  range_addressable (aview tfibsegs (w_H Wc) (ms_mem ms)) SHADOW_OFF res (Z.of_nat (length cs) + 1) ->
  fs_glob tfibsegs Wc (ms_mem ms) (live + (Z.of_nat (length cs) + 1)) (Z.max peak (live + (Z.of_nat (length cs) + 1)))
    (cnt + 1) fail ->
  forall s, YK11.getr (ms_regs ms) 11 = w64 s -> cstr_ok tfibsegs Wc (ms_mem ms) s cs -> cstr_kept B ly S Up s cs ->
  SRr tfibsegs Wc (mkCfg ms mdC)
    (apost_baseU tfibsegs B STK_fuzz_strdup FS_PSTAT_FP regs ly S W mem md 1 Up (Up ++ [(res - HEAD, HEAD)])
      (fun ly' S' W' regs' mem' md' =>
         YK11.getr regs' 10 = w64 res /\ 4096 + HEAD <= res /\
         ablocks B ly' S' = ablocks B ly S ++ [(res - HEAD, Z.of_nat (length cs) + 1 + HEAD)] /\
         fs_heads B ly' S' (Up ++ [(res - HEAD, HEAD)]) /\
         fs_rblock tfibsegs B ly' S' W' mem' res (Z.of_nat (length cs) + 1) /\
         zbytes_at tfibsegs W' mem' res (cs ++ [0]) /\
         fs_glob tfibsegs W' mem' (live + (Z.of_nat (length cs) + 1))
           (Z.max peak (live + (Z.of_nat (length cs) + 1))) (cnt + 1) fail)).
Proof.
intros ly S Up W regs mem md lyc Sc Wc ms mdC res cs live peak cnt fail AMEMCPY HJ HARU HV Hms R1 Rsp R3 R4 R10 R18 R12
  Hkept Hra Eab FH Hres Hrb Hrad HG s R11 Hc Hk.
set (nn := Z.of_nat (length cs) + 1) in *.
set (Uc := Up ++ [(res - HEAD, HEAD)]) in *.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & _ & C3 & _). assert (FS : STK_fuzz_strdup = 16448) by reflexivity.
assert (ESTACK = 4096) as Hes by reflexivity.
pose proof HARU as (HAR & OK & PO).
assert (Hnew : In (res - HEAD, nn + HEAD) (ablocks B lyc Sc)) by (rewrite Eab; apply in_or_app; right; left; reflexivity).
assert (Rq : req_size (nn + HEAD) = nn + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (nn + 16) 0); lia).
destruct (al_blocks _ _ LAWS lyc Sc Wc (unpoison Uc (ms_mem ms)) mdC (res - HEAD) (nn + HEAD) HAR Hnew)
  as (_ & H4096 & Hcl & _ & _ & _ & HMX). rewrite Rq in Hcl.
assert (Hn32 : 0 <= nn < 2 ^ 32) by (unfold MALLOC_MAX, HEAD in *; lia).
pose proof (sd_cpy_disj ly S lyc Sc Wc _ mdC s cs res Up HAR Eab Hk) as Hdisj.
pose proof Hc as (_ & Hs4096 & Hscl & _ & Hsam & Hsra & Hshv & _).
assert (Hra' : YK0s.ret_ok (YK11.getr (ms_regs ms) 1))
  by (rewrite R1; apply ret_ok_even; rewrite unsigned_lit_small by (unfold RA_SD_MEMCPY; lia); reflexivity).
set (Wr := fun a => (res <= a < res + nn) \/ (spZ (ms_regs ms) - ESTACK <= a < spZ (ms_regs ms))).
rewrite Hms. change (Z_to_bv 64 PC_memcpy) with (w64 PC_memcpy).
eapply SRr_bind.
{ apply (fsw_intrin_atU B STK_fuzz_strdup (spZ regs) FS_PSTAT_FP ly S W (unpoison Up mem) md [] lyc Sc Uc Wc (ms_mem ms)
    mdC 1 Uc Wr (YK11.getr (ms_regs ms) 1) (cfg_at tfibsegs PC_memcpy (ms_regs ms) (ms_mem ms) mdC)
    (fun regs' mem' md' => aregs_preserved (ms_regs ms) regs' /\
       (forall i, 0 <= i < nn -> aview tfibsegs (w_H Wc) mem' (res + i) = aview tfibsegs (w_H Wc) (ms_mem ms) (s + i)) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview tfibsegs (w_H Wc) mem' a = aview tfibsegs (w_H Wc) (ms_mem ms) a))
    HJ).
  - eapply SRr_mono.
    + apply (AMEMCPY lyc Sc Uc Wc (ms_regs ms) (ms_mem ms) mdC res s nn).
      * exact (fsw_ecall_preU_at B STK_fuzz_strdup (spZ regs) FS_PSTAT_FP ly S W (unpoison Up mem) md [] lyc Sc Uc Wc
          (ms_mem ms) mdC 1 (ms_regs ms) (-32) HJ HARU Rsp eq_refl ltac:(lia) ltac:(lia) Hra' R3 R4).
      * exact R10.
      * exact R11.
      * exact R12.
      * exact Hn32.
      * unfold HEAD in *; lia.
      * lia.
      * intros a Ha. destruct (sd_dest_bytes lyc Sc Uc Wc (ms_mem ms) mdC res nn HARU Hnew ltac:(lia) a Ha) as (Hp & Hno & Hab).
        split; [exact (apresent_writable tfibsegs _ _ _ Hp)|]. split; [exact Hno|]. rewrite Rsp. lia.
      * exact (sd_dest_amem lyc Sc Wc _ mdC res nn HAR Hnew ltac:(lia)).
      * exact Hrad.
      * intros _. exact (sd_dest_hull lyc Sc Uc Wc (ms_mem ms) mdC res nn HARU Hnew ltac:(lia)).
      * split; [lia|]. split; [lia|]. split.
        { intros a Ha. split.
          - destruct Hc as ((Hg & _) & _). assert (Hj : (Z.to_nat (a - s) < length (cs ++ [0%Z]))%nat) by (rewrite length_app; cbn; lia).
            destruct (Hg _ Hj) as [Hv _]. pose proof (Hv 0%nat ltac:(lia)) as Hb.
            replace (s + Z.of_nat (Z.to_nat (a - s)) + Z.of_nat 0) with a in Hb by lia.
            unfold aview. rewrite Hb. discriminate.
          - rewrite Rsp. lia. }
        split; [exact Hdisj|].
        split; [unfold amem_range in *; lia|].
        split; [exact Hsra|]. intros _. exact Hshv.
    + intros W' c' _ (-> & regs' & mem' & md' & -> & HARU' & HP & Hsame & H10' & Hcpy & Hfr & Hgr).
      split; [reflexivity|]. exists regs', mem', md'.
      split; [unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
      split; [exact HARU'|]. split; [exact Hsame|].
      split; [apply (sd_unpoison_frame Uc Wc (ms_mem ms) mem' Wr); intros a Ha Hn; apply Hfr; [exact Ha | | ];
        intros Hx; apply Hn; [left | right]; exact Hx|].
      split; [exact (sd_unpoison_present Uc (w_H Wc) (ms_mem ms) mem' Hgr)|].
      split; [exact HP|]. split; [exact Hcpy|].
      intros a Ha Hn. apply Hfr; [exact Ha | | ]; intros Hx; apply Hn; [left | right]; exact Hx.
  - (* the copy's destination: awr_byte's new-block arm (in_tmp_block); the scratch window: its stack arm; both inside
       awr_byte0 on the one-text core *)
    intros a [Ha | Ha].
    + assert (Htb : exists b n, In (b, n) (ablocks B lyc Sc) /\ ~ In (b, n) (ablocks B ly S) /\ b <= a < b + req_size n).
      { exists (res - HEAD), (nn + HEAD).
        split; [exact Hnew|]. split; [exact (sd_new_not_old ly S lyc Sc Wc _ mdC res nn HAR Eab ltac:(lia))|].
        rewrite Rq. unfold HEAD in *. lia. }
      first [solve [left; right; right; left; exact Htb] | solve [right; right; left; exact Htb]].
    + rewrite Rsp in Ha. first [solve [left; left; lia] | solve [left; lia]]. }
intros W2 c2 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HARU3 & (HP & Hcpy & Hfr)).
assert (Usp : spZ regs3 = spZ regs - 32).
{ unfold spZ. rewrite (fsw_pres (ms_regs ms) regs3 2%bv HP ltac:(unfold acallee_saved; vm_compute; lia)). exact Rsp. }
assert (KD : forall a, 0 <= a < alloc_ceiling -> ~ (res <= a < res + nn) ->
  aview tfibsegs (w_H Wc) mem3 a = aview tfibsegs (w_H Wc) (ms_mem ms) a).
{ intros a Ha Hn. apply Hfr; [lia|]. intros [Hx|Hx]; [exact (Hn Hx) | rewrite Rsp in Hx; lia]. }
pose proof (fsw_resume_after_rtU B STK_fuzz_strdup (spZ regs) FS_PSTAT_FP ly S W (unpoison Up mem) md [] lyc Sc Uc Wc mem3 md3 1
  (ms_regs ms) regs3 (ms_mem ms) 32 (sd_extra regs) sd_cs RA_SD_MEMCPY HJ3 HARU3 HP Rsp ltac:(lia) ltac:(lia) eq_refl
  ltac:(vm_compute; reflexivity) ltac:(repeat constructor; cbn; lia) (sd_chunks_of_vals regs regs3 _ (spZ regs) HV)
  ltac:(intros a Ha; apply (mbyte_of_aview tfibsegs); apply Hfr; [lia|]; intros [Hx|Hx]; [lia | rewrite Rsp in Hx; lia]))
  as HS3.
rewrite R1.
eapply (sd_ret ly S Up W regs mem md lyc Sc Uc Wc regs3 _ md3 1 (fss_ret RA_SD_MEMCPY 32 sd_cs)); [exact HS3 | reflexivity
  | vm_compute; reflexivity | exact I | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | | exact HARU3
  | exact HJ3 | exact Usp | | exact Hra |].
- lazymatch goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end.
  rewrite fsw_SOff0, (ew_Ereg_nat regs3 _ 18 18%bv eq_refl).
  rewrite (fsw_pres (ms_regs ms) regs3 18%bv HP ltac:(unfold acallee_saved; assert (bv_unsigned (18%bv : bv 5) = 18) as -> by reflexivity; lia)). exact R18.
- intros r Hr H2 H8 H9 H18. rewrite (HP r Hr). exact (Hkept r Hr H2 H8 H9 H18).
- intros regsF memF mdF SBF HF10.
  exact (sd_q2 ly S lyc Sc Up Wc _ mdC (ms_mem ms) mem3 (spZ (ms_regs ms)) live peak cnt fail s cs res HAR Eab FH Hres
    Hrb HG Hc Hcpy (fun a Ha H1 H2 => Hfr a Ha (fun Hx => match Hx with or_introl X => H1 X | or_intror Y => H2 Y end))
    ltac:(rewrite Rsp; lia) regsF memF mdF SBF HF10).
Qed.

(* ---- the fuzz_malloc call (0x82d08): fuzz_malloc_spec (FS_FUZZ_MALLOC_A) at the call, its journal composed into the
   caller's by the core's ajournal_sub (its static arm: FS_PSTAT_FP is image bytes, YCbq.v ajournal_sub over RELOC's
   FP-keyed journal), and the state resumed at 0x82d0c ---- *)
Definition sd_after_malloc (regs : bvmap 5 word) ly S Up W mem md (regsM : bvmap 5 word) (n live peak cnt fail : Z)
  : world tfibsegs -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2 U2 k,
    c2 = mkCfg (YK11.mkst regs2 (Z_to_bv 64 RA_SD_MALLOC) mem2 (YK11.seg_rom tfibsegs)) md2 /\
    st_ok tfibsegs (Ereg regs2 (sd_extra regs)) (fss_ret RA_SD_MALLOC 32 sd_cs)
      (restrict (w_H W2) (YK11.mkst regs2 (Z_to_bv 64 RA_SD_MALLOC) mem2 (YK11.seg_rom tfibsegs))) /\
    ajournal tfibsegs B STK_fuzz_strdup (spZ regs) FS_PSTAT_FP ly S W (unpoison Up mem) md [] ly2 S2 W2
      (unpoison U2 mem2) md2 k /\
    ARU tfibsegs B ly2 S2 U2 W2 mem2 md2 /\ spZ regs2 = spZ regs - 32 /\ aregs_preserved regsM regs2 /\
    ((cnt = fail /\ k = 0 /\ U2 = Up /\ YK11.getr regs2 10 = w64 0 /\ ablocks B ly2 S2 = ablocks B ly S /\
      fs_heads B ly2 S2 Up /\ fs_glob tfibsegs W2 mem2 live peak (cnt + 1) SIZE_MAXZ) \/
     (cnt <> fail /\ k = 1 /\ exists res, U2 = Up ++ [(res - HEAD, HEAD)] /\ YK11.getr regs2 10 = w64 res /\
      4096 + HEAD <= res /\ ablocks B ly2 S2 = ablocks B ly S ++ [(res - HEAD, n + HEAD)] /\
      fs_heads B ly2 S2 (Up ++ [(res - HEAD, HEAD)]) /\ fs_rblock tfibsegs B ly2 S2 W2 mem2 res n /\
      range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF res n /\
      fs_glob tfibsegs W2 mem2 (live + n) (Z.max peak (live + n)) (cnt + 1) fail)).
Lemma sd_malloc_step : forall ly S Up W regs mem md msM mdM n live peak cnt fail,
  @fuzz_malloc_spec fx rc SK tfibsegs B ->
  ARU tfibsegs B ly S Up W mem md -> arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem) ->
  fs_heads B ly S Up ->
  ajournal tfibsegs B STK_fuzz_strdup (spZ regs) FS_PSTAT_FP ly S W (unpoison Up mem) md [] ly S W
    (unpoison Up (ms_mem msM)) mdM 0 ->
  ARU tfibsegs B ly S Up W (ms_mem msM) mdM ->
  sd_frame_vals (mrestrict (w_H W) (ms_mem msM)) (spZ regs) regs ->
  msM = YK11.mkst (ms_regs msM) (Z_to_bv 64 A_fuzz_malloc) (ms_mem msM) (YK11.seg_rom tfibsegs) ->
  YK11.getr (ms_regs msM) 1 = Z_to_bv 64 RA_SD_MALLOC -> spZ (ms_regs msM) = spZ regs - 32 ->
  YK11.getr (ms_regs msM) 3 = w64 (as_gp B) -> YK11.getr (ms_regs msM) 4 = w64 (as_tp B) ->
  s0Z (ms_regs msM) < alloc_ceiling ->
  YK11.getr (ms_regs msM) 10 = w64 n -> 1 <= n -> n + HEAD < MALLOC_MAX ->
  fs_glob tfibsegs W (ms_mem msM) live peak cnt fail -> (cnt <> fail -> live + n < 2 ^ 64) -> cnt + 1 < 2 ^ 64 ->
  st_nev S + 1 <= EV_MAX -> (cnt <> fail -> blocks_bytes S + (n + HEAD) <= LIVE_MAX) ->
  SRr tfibsegs W (mkCfg msM mdM) (sd_after_malloc regs ly S Up W mem md (ms_regs msM) n live peak cnt fail).
Proof.
intros ly S Up W regs mem md msM mdM n live peak cnt fail MALLOC H0 HR FH HJ HARU HV Hms R1 Rsp R3 R4 Hs0 R10 Hn1 Hnm
  HG Hlv Hcn Hev Hlb.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & _ & C3 & _).
assert (FS : STK_fuzz_strdup = 16448) by reflexivity. assert (FM : STK_fuzz_malloc = 16416) by reflexivity.
pose proof (sd_malloc_pre ly S Up W regs mem md ly S W (ms_regs msM) (ms_mem msM) mdM 0 H0 HARU HJ HR Rsp R1 R3 R4 Hs0)
  as HPRE.
rewrite Hms. change (Z_to_bv 64 A_fuzz_malloc) with (w64 A_fuzz_malloc).
eapply SRr_mono.
{ apply (MALLOC ly S Up W (ms_regs msM) (ms_mem msM) mdM [] n live peak cnt fail HPRE FH).
  all: first [ solve [exact R10] | solve [exact Hnm] | solve [exact HG] | solve [exact Hlv] | solve [exact Hcn]
             | solve [exact Hev] | solve [exact Hlb] | solve [lia] ]. }
intros W2 c2 Hle Hpost.
(* the composition and the resumed state, common to both arms *)
assert (COMP : forall k1 U2 Q2, apost_baseU tfibsegs B STK_fuzz_malloc FS_PSTAT_FP (ms_regs msM) ly S W (ms_mem msM) mdM k1
    Up U2 Q2 W2 c2 ->
  exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (YK11.mkst regs2 (Z_to_bv 64 RA_SD_MALLOC) mem2 (YK11.seg_rom tfibsegs)) md2 /\
    st_ok tfibsegs (Ereg regs2 (sd_extra regs)) (fss_ret RA_SD_MALLOC 32 sd_cs)
      (restrict (w_H W2) (YK11.mkst regs2 (Z_to_bv 64 RA_SD_MALLOC) mem2 (YK11.seg_rom tfibsegs))) /\
    ajournal tfibsegs B STK_fuzz_strdup (spZ regs) FS_PSTAT_FP ly S W (unpoison Up mem) md [] ly2 S2 W2
      (unpoison U2 mem2) md2 (0 + k1) /\
    ARU tfibsegs B ly2 S2 U2 W2 mem2 md2 /\ spZ regs2 = spZ regs - 32 /\ aregs_preserved (ms_regs msM) regs2 /\
    Q2 ly2 S2 W2 regs2 mem2 md2).
{ intros k1 U2 Q2 (ly2 & S2 & regs2 & mem2 & md2 & Ec & HJc & OK2 & PO2 & HP & HQ).
  destruct (fsw_after_callFPU B STK_fuzz_strdup (spZ regs) FS_PSTAT_FP [] ly S Up W mem md W ly S Up (ms_mem msM) mdM 0
    STK_fuzz_malloc FS_PSTAT_FP 32 (ms_regs msM) ly2 S2 U2 W2 regs2 mem2 md2 k1 (sd_extra regs) sd_cs RA_SD_MALLOC HJ HARU HJc)
    as (HJ2 & HARU2 & HS2);
    (* one solve per premise kind; the computing alternatives only on the goal shape they are for (vm_compute or cbn on
       a goal that mentions tfibsegs would normalize the image) *)
    first [ solve [exact OK2] | solve [exact PO2] | solve [exact HP] | solve [exact Rsp]
          | lazymatch goal with |- fsw_fp_sub _ _ _ _ _ _ _ _ =>
              solve [intros a Ha; right; right; left; split; [exact Ha | exact (sd_pstat_img a Ha)]] end
          | lazymatch goal with |- Forall (YP09.chunk_ok _ _ _ _) _ =>
              solve [exact (sd_chunks_of_vals regs regs2 _ (spZ regs) HV)] end
          | lazymatch goal with |- regions_wf _ = true => solve [vm_compute; reflexivity] end
          | lazymatch goal with |- Forall (fun _ => _) sd_cs => solve [repeat constructor; cbn; lia] end
          | lazymatch goal with |- _ mod _ = _ => solve [reflexivity] end
          | lazymatch goal with |- ?a <= ?b => solve [lia] | |- ?a < ?b => solve [lia] end
          | idtac ].
  assert (Usp : spZ regs2 = spZ regs - 32).
  { unfold spZ. rewrite (fsw_pres (ms_regs msM) regs2 2%bv HP ltac:(unfold acallee_saved; vm_compute; lia)). exact Rsp. }
  exists ly2, S2, regs2, mem2, md2.
  split; [rewrite Ec, R1; reflexivity|].
  split; [exact HS2|].
  split; [exact HJ2|]. split; [exact HARU2|]. split; [exact Usp|]. split; [exact HP | exact HQ]. }
destruct Hpost as [(Hcf & HA) | (Hcf & res & HA)].
- destruct (COMP 0 Up _ HA) as (ly2 & S2 & regs2 & mem2 & md2 & Ec & HS2 & HJ2 & HARU2 & Usp & HP & Q10 & Qab & Qfh & Qg).
  exists ly2, S2, regs2, mem2, md2, Up, 0.
  split; [exact Ec|]. split; [exact HS2|]. split; [exact HJ2|]. split; [exact HARU2|]. split; [exact Usp|].
  split; [exact HP|]. left. split; [exact Hcf|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact Q10|]. split; [exact Qab|]. split; [exact Qfh | exact Qg].
- destruct (COMP 1 _ _ HA) as (ly2 & S2 & regs2 & mem2 & md2 & Ec & HS2 & HJ2 & HARU2 & Usp & HP & Q10 & Qr & Qab & Qfh
    & Qrb & Qra & Qg).
  exists ly2, S2, regs2, mem2, md2, (Up ++ [(res - HEAD, HEAD)]), 1.
  split; [exact Ec|]. split; [exact HS2|]. split; [exact HJ2|]. split; [exact HARU2|]. split; [exact Usp|].
  split; [exact HP|]. right. split; [exact Hcf|]. split; [reflexivity|]. exists res.
  split; [reflexivity|]. split; [exact Q10|]. split; [exact Qr|]. split; [exact Qab|]. split; [exact Qfh|].
  split; [exact (Qrb ltac:(lia))|]. split; [exact Qra | exact Qg].
Qed.

(* fs_glob carried across a call whose frame keeps every byte below alloc_ceiling (aview form) *)
Lemma sd_fs_glob_av : forall (W : world tfibsegs) m m' live peak cnt fail,
  (forall a, 0 <= a < alloc_ceiling -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W m' live peak cnt fail.
Proof.
intros W m m' live peak cnt fail Hk (G1 & G2 & G3 & G4 & R). pose proof asan_consts as (C1 & _).
assert (VK : forall a v, 0 <= a -> a + 8 <= alloc_ceiling -> val_mem tfibsegs (mrestrict (w_H W) m) a 8 v ->
  val_mem tfibsegs (mrestrict (w_H W) m') a 8 v).
{ intros a v Ha Hb Hv. apply (val_mem_kept tfibsegs (w_H W) (w_H W) m m'); first [solve [exact Hv] | idtac].
  intros j Hj. apply Hk. lia. }
unfold fs_glob, fs_glob_at, G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
split; [apply VK; [lia | lia | exact G1]|]. split; [apply VK; [lia | lia | exact G2]|].
split; [apply VK; [lia | lia | exact G3]|]. split; [apply VK; [lia | lia | exact G4] | exact R].
Qed.
Lemma sd_getr_z : forall (rg : bvmap 5 word) (r : bv 5) z, bv_unsigned r = z -> YK11.getr rg r = YK11.getr rg (Z_to_bv 5 z).
Proof. intros rg r z E. rewrite <- E, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma sd_w64_of_unsigned : forall (x : word) v, bv_unsigned x = v -> x = w64 v.
Proof. intros x v E. unfold w64. rewrite <- E. symmetry. apply Z_to_bv_bv_unsigned. Qed.
End w.

(* ---- the walk ---- *)
Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the image facts (FSH_Fn_FORM.md section 1); owner RELOC (proved once for fs's TfibB) *)
Hypothesis IMG : fs_img_facts tfibsegs B.
(* the strlen interceptor at PC_strlen 0x42654 in ARU form (FSH_Gen.astrlen_realizesU, FSH_Rt.FsRt.fr_strlen); owner the
   shared runtime (RUNTIME-str lane) *)
Hypothesis FS_ASTRLEN_A : astrlen_realizesU tfibsegs B PC_strlen.
(* __asan_memcpy at PC_memcpy 0x51d20 in ARU form (FSupoisonU.aintrin_realizesU OCpy); owner the shared runtime
   (a Theorem Labs lane's U twin of the donor's aintrin_realizes, a Theorem Labs lane) *)
Hypothesis FS_AMEMCPY_A : FSupoisonU.aintrin_realizesU tfibsegs B OCpy PC_memcpy.
(* fuzz_malloc's contract (no CTX since stage 1 of the fold; the one call returns to 0x82d0c with an empty chain: s0
   holds the string pointer); owner a Theorem Labs lane (a Theorem Labs lane's ALLOC group), discharged at composition by
   fuzz_malloc_holds (a working branch 8989ddd6cb6) *)
Hypothesis FS_FUZZ_MALLOC_A : @fuzz_malloc_spec fx rc SK tfibsegs B.

Theorem fuzz_strdup_holds : @fuzz_strdup_spec fx rc SK tfibsegs B.
Proof.
intros ly S U W regs mem md ch s cs live peak cnt fail HPRE FH H10 Hc Hk Hstkd HG Hlv Hcn Hmx Hev Hlb.
pose proof HPRE as ((HAP & OK & PO) & HRO).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (fsw_ARU B STK_fuzz_strdup ly S U W regs mem md ch (proj1 HPRE)) as H0.
pose proof Hc as (_ & Hs4096 & Hscl & Hs32 & _).
pose proof asan_consts as (C1 & _).
set (len := Z.of_nat (length cs)) in *.
apply (sd_to_strlen B ly S U W regs mem md ch _ HPRE).
intros ms mat HS HJ HARU SB HV Hms R1 Rsp R8 R10 R3 R4 Rk.
apply (sd_strlen_step B ly S U W regs mem md ms _ s cs _ FS_ASTRLEN_A IMG H0 HRO HJ HARU SB HV Hms R1 Rsp
  ltac:(rewrite R10; exact H10) ltac:(rewrite R3; exact Hgp) ltac:(rewrite R4; exact Htp) Hc).
intros regs1 mem1 md1 HS1 HJ1 HARU1 Usp1 H101 HP1 Hav1.
assert (U101 : bv_unsigned (YK11.getr regs1 10) = len).
{ rewrite H101. unfold w64. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|]. change (bv_modulus 64) with (2 ^ 64). lia. }
apply (sd_to_malloc B regs ly S U W mem md ly S W regs1 mem1 md1 0 _ HS1 HARU1 HJ1 Usp1 ltac:(lia)).
intros msM matM HSM HJM HARUM SBM HVM HmsM R1M RspM R10M R9M RkM.
(* register facts at the malloc call, back to the entry registers *)
assert (P1 : forall z, acallee_saved z -> YK11.getr regs1 (Z_to_bv 5 z) = YK11.getr (ms_regs ms) (Z_to_bv 5 z)) by exact HP1.
assert (GM : forall z, 0 < z < 32 -> z <> 1 -> z <> 2 -> z <> 8 -> z <> 9 -> z <> 10 -> acallee_saved z ->
  YK11.getr (ms_regs msM) (Z_to_bv 5 z) = YK11.getr regs (Z_to_bv 5 z)).
{ intros z Hz H1 H2 H8 H9 H10' Hcs. rewrite (RkM z Hz H1 H9 H10'), (P1 z Hcs). exact (Rk z Hcs H2 H8). }
assert (R3M : YK11.getr (ms_regs msM) 3 = w64 (as_gp B))
  by (rewrite (sd_getr_z _ 3%bv 3 eq_refl); rewrite (GM 3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold acallee_saved; lia)); exact Hgp).
assert (R4M : YK11.getr (ms_regs msM) 4 = w64 (as_tp B))
  by (rewrite (sd_getr_z _ 4%bv 4 eq_refl); rewrite (GM 4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold acallee_saved; lia)); exact Htp).
assert (R8M : YK11.getr (ms_regs msM) 8 = w64 s).
{ rewrite (sd_getr_z _ 8%bv 8 eq_refl), (RkM 8 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)),
    (P1 8 ltac:(unfold acallee_saved; lia)), <- (sd_getr_z _ 8%bv 8 eq_refl), <- H10. exact R8. }
assert (R10M' : YK11.getr (ms_regs msM) 10 = w64 (len + 1)) by (apply sd_w64_of_unsigned; rewrite R10M, U101; reflexivity).
assert (Hs0 : s0Z (ms_regs msM) < alloc_ceiling).
{ unfold s0Z. rewrite R8M. unfold w64. rewrite Z_to_bv_unsigned, bv_wrap_small; [lia|]. change (bv_modulus 64) with (2 ^ 64). lia. }
assert (HGM : fs_glob tfibsegs W (ms_mem msM) live peak cnt fail).
{ apply (fs_glob_below W mem1 (ms_mem msM) _ _ _ _ SBM). apply (sd_fs_glob_av W (ms_mem ms) mem1 _ _ _ _ Hav1).
  exact (fs_glob_below W mem (ms_mem ms) _ _ _ _ SB HG). }
eapply SRr_bind.
{ exact (sd_malloc_step B ly S U W regs mem md msM _ (len + 1) live peak cnt fail FS_FUZZ_MALLOC_A H0 HRO FH HJM HARUM HVM
    HmsM R1M RspM R3M R4M Hs0 R10M' ltac:(lia) ltac:(unfold HEAD in *; lia) HGM
    ltac:(intros Hne; pose proof (Hlv Hne); lia) Hcn Hev ltac:(intros Hne; pose proof (Hlb Hne); lia)). }
intros W2 c2 Hle (ly2 & S2 & regs2 & mem2 & md2 & U2 & k & -> & HS2 & HJ2 & HARU2 & Usp2 & HP2 & Harm).
(* the callee-saved registers fuzz_strdup leaves alone hold their entry values after fuzz_malloc *)
assert (Hkept2 : sd_kept regs regs2).
{ intros z Hz H2 H8 H9 H18. rewrite (HP2 z Hz).
  assert (Hz' : 0 < z < 32 /\ z <> 1 /\ z <> 10) by (unfold acallee_saved in Hz; lia).
  exact (GM z ltac:(lia) ltac:(lia) H2 H8 H9 ltac:(lia) Hz). }
destruct Harm as [(Hcf & -> & -> & H102 & Hab & Hfh & Hg2) | (Hcf & -> & res & -> & H102 & Hres & Hab & Hfh & Hrb & Hrad & Hg2)].
- (* NULL arm *)
  eapply SRr_mono.
  { apply (sd_null_arm B ly S U W regs mem md ly2 S2 U W2 regs2 mem2 md2 0
      (fun ly' S' W' regs' mem' md' => YK11.getr regs' 10 = w64 0 /\ ablocks B ly' S' = ablocks B ly S /\
         fs_heads B ly' S' U /\ fs_glob tfibsegs W' mem' live peak (cnt + 1) SIZE_MAXZ)
      HS2 HARU2 HJ2 Usp2 Hkept2 Hra H102).
    intros regsF memF mdF SBF HF10. split; [exact HF10|]. split; [exact Hab|]. split; [exact Hfh|].
    exact (fs_glob_below W2 mem2 memF _ _ _ _ SBF Hg2). }
  intros W' c' _ HQ. left. split; [exact Hcf | exact HQ].
- (* the copy arm *)
  assert (Hres64 : 0 <= res < 2 ^ 64).
  { destruct Hrb as (Hin & _). destruct (al_blocks _ _ (AR_laws_ok tfibsegs B) ly2 S2 W2 (unpoison (U ++ [(res - HEAD, HEAD)]) mem2) md2
      _ _ (proj1 HARU2) Hin) as (_ & H4096 & Hcl & _).
    pose proof (req_size_pos (len + 1 + HEAD) ltac:(unfold HEAD; lia)). unfold HEAD in *. lia. }
  assert (H10ne : YK11.getr regs2 10 <> w64 0).
  { rewrite H102. intros E. apply (f_equal bv_unsigned) in E. unfold w64 in E.
    rewrite !Z_to_bv_unsigned, !bv_wrap_small in E by (change (bv_modulus 64) with (2 ^ 64); lia). unfold HEAD in *. lia. }
  pose proof (sd_cstr_after B STK_fuzz_strdup (spZ regs) ly S U W mem md ly2 S2 W2 mem2 md2 1 s cs res (len + 1) IMG H0 HARU2 HJ2
    HRO Hab ltac:(lia) Hk Hc) as Hc2.
  eapply SRr_mono.
  { apply (sd_to_memcpy B regs ly S U W mem md ly2 S2 (U ++ [(res - HEAD, HEAD)]) W2 regs2 mem2 md2 1 _ HS2 HARU2 HJ2 Usp2
      H10ne).
    intros msC matC HSC HJC HARUC SBC HVC HmsC R1C RspC R10C R11C R12C R18C RkC.
    assert (GC : forall z, 0 < z < 32 -> z <> 1 -> z <> 11 -> z <> 12 -> z <> 18 -> acallee_saved z -> z <> 2 -> z <> 8 ->
      z <> 9 -> YK11.getr (ms_regs msC) (Z_to_bv 5 z) = YK11.getr regs (Z_to_bv 5 z)).
    { intros z Hz H1 H11 H12 H18 Hcs H2 H8 H9. rewrite (RkC z Hz H1 H11 H12 H18). exact (Hkept2 z Hcs H2 H8 H9 H18). }
    apply (sd_memcpy_step B ly S U W regs mem md ly2 S2 W2 msC _ res cs live peak cnt fail FS_AMEMCPY_A HJC HARUC HVC HmsC R1C
      RspC) with (s := s).
    - rewrite (sd_getr_z _ 3%bv 3 eq_refl). rewrite (GC 3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold acallee_saved; lia) ltac:(lia)
        ltac:(lia) ltac:(lia)). exact Hgp.
    - rewrite (sd_getr_z _ 4%bv 4 eq_refl). rewrite (GC 4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold acallee_saved; lia) ltac:(lia)
        ltac:(lia) ltac:(lia)). exact Htp.
    - rewrite R10C. exact H102.
    - rewrite R18C. exact H102.
    - rewrite R12C. apply sd_w64_of_unsigned.
      rewrite (sd_getr_z _ 9%bv 9 eq_refl), (HP2 9 ltac:(unfold acallee_saved; lia)), <- (sd_getr_z _ 9%bv 9 eq_refl).
      rewrite R9M, U101. reflexivity.
    - intros z Hz H2 H8 H9 H18. pose proof Hz as Hz'. unfold acallee_saved in Hz'. apply GC; try lia; exact Hz.
    - exact Hra.
    - exact Hab.
    - exact Hfh.
    - exact Hres.
    - destruct Hrb as (Hin & H16 & Hn & Hv). split; [exact Hin|]. split; [exact H16|]. split; [exact Hn|].
      apply (val_mem_below (w_H W2) mem2 (ms_mem msC) alloc_ceiling _ 8 _ SBC);
        first [solve [exact Hv] | solve [unfold HEAD in *; lia] | idtac].
      destruct (al_blocks _ _ (AR_laws_ok tfibsegs B) ly2 S2 W2 (unpoison (U ++ [(res - HEAD, HEAD)]) mem2) md2 _ _ (proj1 HARU2) Hin)
        as (_ & H4096 & Hcl & _). pose proof (req_size_pos (len + 1 + HEAD) ltac:(unfold HEAD; lia)). unfold HEAD in *. lia.
    - apply (sd_range_addressable_below (w_H W2) mem2 (ms_mem msC) res (len + 1) SBC); [lia | | exact Hrad].
      destruct Hrb as (Hin & _).
      destruct (al_blocks _ _ (AR_laws_ok tfibsegs B) ly2 S2 W2 (unpoison (U ++ [(res - HEAD, HEAD)]) mem2) md2 _ _ (proj1 HARU2) Hin)
        as (_ & H4096 & Hcl & _). pose proof (req_size_pos (len + 1 + HEAD) ltac:(unfold HEAD; lia)). unfold HEAD in *. lia.
    - exact (fs_glob_below W2 mem2 (ms_mem msC) _ _ _ _ SBC Hg2).
    - rewrite R11C, (sd_getr_z _ 8%bv 8 eq_refl), (HP2 8 ltac:(unfold acallee_saved; lia)), <- (sd_getr_z _ 8%bv 8 eq_refl).
      exact R8M.
    - exact (cstr_ok_below W2 mem2 (ms_mem msC) s cs SBC Hc2).
    - exact Hk. }
  intros W' c' _ HQ. right. split; [exact Hcf|]. exists res. exact HQ.
Qed.
End m.
