(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 848 of its 931 lines of code are new or changed and 1841 lines of the source are left out. *)
(* has_prefixed 0x82130..0x822c4 (lv2_locate.c:55-76) in fm.asan, walk kit (G2): the code table, the symbolic states
   the walk seats, the loop state hp_st with its continuation form hp_cont, the statements of the five loop segments
   (seg_*_ok: the frozen interface between the segment files FMW_hp_seg*.v and the loop proof FMW_has_prefixed.v),
   and the lemmas every segment uses: seats, the C-string facts at any state of the walk, the shadow-check entry, the
   runtime-call and name_char-call steps, and the epilogue. Control flow and loop invariant follow fm's released plain
   proof lib/Prog/has_prefixed.v (hp_loop :138); the inline ASan checks run on the donor's token engine (YCbq.v
   aj_run_tok) with one shadow entry for the checked byte. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI04 YN3v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YA0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC20 YI16 YI00 YM05 YG0q YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_g2rt FMW_name_char.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel has_prefixed_model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- code table ---- *)
Definition HP_LEN : nat := 101.
Definition tbl_hp : ctable := Eval vm_compute in build_table tfibsegs A_has_prefixed HP_LEN TEmpty.
Lemma tbl_hp_eq : tbl_hp = build_table tfibsegs A_has_prefixed HP_LEN TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_hp). Qed.
Lemma tbl_hp_ok : table_ok tfibsegs tbl_hp.
Proof. rewrite tbl_hp_eq. apply build_table_ok; [cbv; discriminate | apply table_ok_empty]. Qed.

(* ---- program points ---- *)
Definition HP_HEAD : Z := 0x821b0.   (* loop head: a0 = at - t; blt a0, plen + 1 *)
Definition HP_NCMP : Z := 0x821dc.   (* at[-1] = ':' : strncmp (start, prefix, plen) *)
Definition HP_PRE : Z := 0x821f0.    (* prefix matched: the byte before start *)
Definition HP_POST : Z := 0x82220.   (* the byte after the location *)
Definition HP_TAIL : Z := 0x82240.   (* next occurrence: strstr (at + 1, location) *)
Definition A_hp_epi : Z := 0x82280.  (* epilogue, a0 = the answer *)

(* ---- the entry state (prologue, the shadow base from the GOT) ---- *)
Definition SBz : Z := 0x7fff8000.
Definition hp_got_region : YP09.region :=
  YP09.mkRegion None A_GOT_shadow (A_GOT_shadow + 8) 0 0
    [YP09.mkChunk A_GOT_shadow (CVal 8 (SLit A_shadow_glob))].
Definition hp_cell_region : YP09.region :=
  YP09.mkRegion None A_shadow_glob (A_shadow_glob + 8) 0 0
    [YP09.mkChunk A_shadow_glob (CVal 8 (SOff 32 0))].
Definition hp_regions : smem :=
  [YP09.mkRegion (Some 2%nat) (-112) 0 (-112) 0 []; hp_got_region; hp_cell_region].
Definition hp_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SBz SBz 0)] [] [].
Definition ss_hp : sstate := mkSS A_has_prefixed sr_atoms hp_regions None hp_facts.
Definition hp_Bx : sv := SOff 32 0.
Definition hp_Bspan : Z * Z := (SBz, SBz + 2 ^ 44 - 1).

(* the epilogue state: sp = sp0 - 112, the 13 saved words at sp + 8 .. sp + 104 (ra at +104, s0 at +96, .., s11 at +8)
   are the extra atoms 33..45 *)
Definition hp_frame_region : YP09.region :=
  YP09.mkRegion (Some 2%nat) 8 112 8 112
    [YP09.mkChunk 8 (CVal 8 (SOff 45 0)); YP09.mkChunk 16 (CVal 8 (SOff 44 0));
     YP09.mkChunk 24 (CVal 8 (SOff 43 0)); YP09.mkChunk 32 (CVal 8 (SOff 42 0));
     YP09.mkChunk 40 (CVal 8 (SOff 41 0)); YP09.mkChunk 48 (CVal 8 (SOff 40 0));
     YP09.mkChunk 56 (CVal 8 (SOff 39 0)); YP09.mkChunk 64 (CVal 8 (SOff 38 0));
     YP09.mkChunk 72 (CVal 8 (SOff 37 0)); YP09.mkChunk 80 (CVal 8 (SOff 36 0));
     YP09.mkChunk 88 (CVal 8 (SOff 35 0)); YP09.mkChunk 96 (CVal 8 (SOff 34 0));
     YP09.mkChunk 104 (CVal 8 (SOff 33 0))].
Definition hp_loop_regions : smem := [hp_frame_region; hp_got_region; hp_cell_region].
Definition ss_hp_at (pc : Z) : sstate := mkSS pc sr_atoms hp_loop_regions None hp_facts.

(* the segment states: registers only (every runtime value an atom, no memory region: the loop body stores nothing);
   for an inline check, a0 = the checked address (atom 10), the checked byte's one-byte region, its value atom 32, the
   shadow base s7 = atom 23 (hc_Bx) and one shadow entry covering the byte (hc_SH) *)
Definition hs_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (23%nat, mkAF SBz SBz 0)] [] [].
Definition ss_hs (pc : Z) : sstate := mkSS pc sr_atoms [] None hs_facts.
Definition hc_region : YP09.region := YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition hc_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (23%nat, mkAF SBz SBz 0); (10%nat, mkAF 4096 (2 ^ 47 - 8) 0)] [] [].
Definition ss_hc (pc : Z) : sstate := mkSS pc sr_atoms [hc_region] None hc_facts.
Definition hc_Bx : sv := SOff 23 0.
Definition hc_SH : list shent := [mkSHE 10 0 1].

(* the registers a walk step keeps (callee-saved but s5 = at, s6, s9, which the loop rewrites) *)
Definition HP_KEEP : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 23; 24; 26; 27]%bv.
Definition regs_keep (L : list (bv 5)) (regs regs' : bvmap 5 word) : Prop :=
  forall r, In r L -> getr regs' r = getr regs r.

Ltac ceil2 := pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR; unfold YG0f.ASAN_CEIL in CR.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Hypothesis TL : TfibLib B.
Hypothesis IMGF : fm_img_facts tfibsegs B.

Lemma regs_keep_of_st_ok : forall L E ss ms regs0 extra,
  st_ok tfibsegs E ss ms -> env_agree 32 (Ereg regs0 extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) L = true ->
  regs_keep L regs0 (ms_regs ms).
Proof.
intros L E ss ms regs0 extra HS [HA _] Hcs r Hin.
pose proof (proj1 (forallb_forall _ _) Hcs _ Hin) as Hq. cbn beta in Hq. apply sv_eqb_eq in Hq.
rewrite (st_ok_reg tfibsegs E ss ms _ HS), Hq. cbn [sv_denot]. rewrite Z.add_0_r.
rewrite HA. 2:{ pose proof (u5_range r). lia. }
rewrite ew_Ereg_reg, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma regs_keep_of_preserved : forall regs regs', aregs_preserved regs regs' -> regs_keep HP_KEEP regs regs'.
Proof.
intros regs regs' HP r Hr.
assert (Hc : acallee_saved (bv_unsigned r)).
{ cbv [HP_KEEP In] in Hr. unfold acallee_saved.
  repeat (destruct Hr as [<- | Hr];
    [lazymatch goal with |- context [bv_unsigned ?b] =>
       let v := eval vm_compute in (bv_unsigned b) in change (bv_unsigned b) with v end; lia |]).
  destruct Hr. }
pose proof (HP (bv_unsigned r) Hc) as E. rewrite Z_to_bv_bv_unsigned in E. exact E.
Qed.

(* ---- the 13 saved words, as the epilogue reads them back ---- *)
Definition hp_frame (W : world tfibsegs) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  val_mem tfibsegs (mrestrict (w_H W) m) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) /\
  val_mem tfibsegs (mrestrict (w_H W) m) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) /\
  val_mem tfibsegs (mrestrict (w_H W) m) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) /\
  val_mem tfibsegs (mrestrict (w_H W) m) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) /\
  val_mem tfibsegs (mrestrict (w_H W) m) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) /\
  val_mem tfibsegs (mrestrict (w_H W) m) (spZ regs - 48) 8 (bv_unsigned (getr regs 20)) /\
  val_mem tfibsegs (mrestrict (w_H W) m) (spZ regs - 56) 8 (bv_unsigned (getr regs 21)) /\
  val_mem tfibsegs (mrestrict (w_H W) m) (spZ regs - 64) 8 (bv_unsigned (getr regs 22)) /\
  val_mem tfibsegs (mrestrict (w_H W) m) (spZ regs - 72) 8 (bv_unsigned (getr regs 23)) /\
  val_mem tfibsegs (mrestrict (w_H W) m) (spZ regs - 80) 8 (bv_unsigned (getr regs 24)) /\
  val_mem tfibsegs (mrestrict (w_H W) m) (spZ regs - 88) 8 (bv_unsigned (getr regs 25)) /\
  val_mem tfibsegs (mrestrict (w_H W) m) (spZ regs - 96) 8 (bv_unsigned (getr regs 26)) /\
  val_mem tfibsegs (mrestrict (w_H W) m) (spZ regs - 104) 8 (bv_unsigned (getr regs 27)).

(* ---- pure facts ---- *)
(* an occurrence in a suffix is a match in the whole text *)
Lemma occ_at_mt : forall (t w : list Z) b j, (b <= length t)%nat -> occ_at (skipn b t) w j ->
  has_prefixed_model.mt t w (b + j) = true.
Proof.
intros t w b j Hb (Hl & He). rewrite <- (has_prefixed_model.mt_skipn t w b j Hb). unfold has_prefixed_model.mt.
apply andb_true_iff. split; [apply Nat.leb_le; exact Hl|]. rewrite He. apply ManifestModel.zl_eqb_refl.
Qed.
Lemma mt_occ_at : forall (t w : list Z) b j, (b <= length t)%nat -> has_prefixed_model.mt t w (b + j) = true ->
  occ_at (skipn b t) w j.
Proof.
intros t w b j Hb H. rewrite <- (has_prefixed_model.mt_skipn t w b j Hb) in H. unfold has_prefixed_model.mt in H.
apply andb_true_iff in H as [H1 H2]. split; [apply Nat.leb_le; exact H1|].
apply ManifestModel.zl_eqb_eq. exact H2.
Qed.
(* the shadow hull of a sub-range lies in the hull of the range (as G5's FMW_kitS.v shadow_hull_vis_sub) *)
Lemma g2_hull_sub : forall rd x n x' n',
  shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> 0 < n' -> shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 H3 s Hs. apply H. unfold shadow_addr, SHADOW_OFF in *.
assert (M1 : (2147450880 + x / 8) / 8 <= (2147450880 + x' / 8) / 8)
  by (apply Z.div_le_mono; [lia|]; pose proof (Z.div_le_mono x x' 8 ltac:(lia) H1); lia).
assert (M2 : (2147450880 + (x' + n' - 1) / 8) / 8 <= (2147450880 + (x + n - 1) / 8) / 8)
  by (apply Z.div_le_mono; [lia|]; pose proof (Z.div_le_mono (x' + n' - 1) (x + n - 1) 8 ltac:(lia) ltac:(lia)); lia).
lia.
Qed.
(* a suffix of a C string is a C string with the same NUL (as G5's FMW_kitS.v cstr_ok_suffix) *)
Lemma g2_cstr_suffix : forall (W : world tfibsegs) mem p0 l0 k, (k <= length l0)%nat ->
  cstr_ok tfibsegs W mem p0 l0 -> cstr_ok tfibsegs W mem (p0 + Z.of_nat k) (skipn k l0).
Proof.
intros W mem p0 l0 k Hk ((Hg & Hnz) & H4096 & Hcl & H32 & Ham & Hra & Hhv & Htl).
assert (Hlen : Z.of_nat (length (skipn k l0)) = Z.of_nat (length l0) - Z.of_nat k) by (rewrite length_skipn; lia).
assert (Eend : p0 + Z.of_nat k + Z.of_nat (length (skipn k l0)) = p0 + Z.of_nat (length l0)) by lia.
split; [split|].
- rewrite <- (firstn_skipn k l0) in Hg. rewrite <- app_assoc in Hg. apply (garr8_app tfibsegs) in Hg as [_ Hg].
  rewrite length_firstn in Hg. replace (Nat.min k (length l0)) with k in Hg by lia. exact Hg.
- rewrite <- (firstn_skipn k l0) in Hnz. apply Forall_app in Hnz as [_ Hnz]. exact Hnz.
- split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold amem_range in *; lia|].
  split; [intros x Hx; apply Hra; lia|].
  split; [apply (g2_hull_sub _ p0 (Z.of_nat (length l0) + 1)); [exact Hhv | lia | lia | lia]|].
  intros a Ha. rewrite Eend in Ha. exact (Htl a Ha).
Qed.
(* the bytes of a C string, with its NUL at index length *)
Lemma cstr_byte : forall (W : world tfibsegs) mem p l i, cstr tfibsegs W mem p l -> (i <= length l)%nat ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (p + Z.of_nat i) 1 (ManifestModel.byte_at l i) /\
  0 <= ManifestModel.byte_at l i < 256.
Proof.
intros W mem p l i (Hg & _) Hi.
assert (Hi' : (i < length (l ++ [0%Z]))%nat) by (rewrite length_app; cbn; lia).
destruct (Hg i Hi') as [Hv Hr].
assert (E : nth i (l ++ [0]) 0 = ManifestModel.byte_at l i).
{ unfold ManifestModel.byte_at. destruct (Nat.lt_ge_cases i (length l)) as [Hl|Hl].
  - rewrite app_nth1 by exact Hl. reflexivity.
  - replace i with (length l) by lia. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn.
    rewrite nth_overflow by lia. reflexivity. }
rewrite E in Hv, Hr. split; assumption.
Qed.


(* ---- the walk's context: the entry state and the arguments ---- *)
Record hpcx : Type := mkHC {
  cx_regs0 : bvmap 5 word; cx_ly : alayout; cx_S : astate; cx_W0 : world tfibsegs;
  cx_mem : word -> option byte; cx_md : Model;
  cx_t : Z; cx_q : Z; cx_plen : Z; cx_lp : Z; cx_tb : list Z; cx_lb : list Z;
  cx_live : Z; cx_peak : Z; cx_cnt : Z; cx_fail : Z }.
Definition cx_pre (cx : hpcx) : list Z := firstn (Z.to_nat (cx_plen cx)) (skipn (Z.to_nat (cx_q cx)) (cx_tb cx)).
Definition hp_res (cx : hpcx) : Z := if ManifestModel.token (cx_tb cx) (cx_pre cx) (cx_lb cx) then 1 else 0.
(* has_prefixed_spec's post (FMH_Fn.v:201) *)
Definition hp_Q (cx : hpcx) : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly2 S2 W2 regs2 mem2 md2 =>
    getr regs2 10 = w64 (hp_res cx) /\ ablocks B ly2 S2 = ablocks B (cx_ly cx) (cx_S cx) /\
    fm_glob tfibsegs W2 mem2 (cx_live cx) (cx_peak cx) (cx_cnt cx) (cx_fail cx).
Definition hp_post (cx : hpcx) : world tfibsegs -> config -> Prop :=
  apost_base tfibsegs B STK_has_prefixed [] (cx_regs0 cx) (cx_ly cx) (cx_S cx) (cx_W0 cx) (cx_mem cx) (cx_md cx) 0
    (hp_Q cx).
(* the entry facts has_prefixed_spec gives *)
Definition hp_entry_ok (cx : hpcx) : Prop :=
  YK0s.ret_ok (getr (cx_regs0 cx) 1) /\ getr (cx_regs0 cx) 3 = w64 (as_gp B) /\ getr (cx_regs0 cx) 4 = w64 (as_tp B) /\
  cstr_ok tfibsegs (cx_W0 cx) (cx_mem cx) (cx_t cx) (cx_tb cx) /\
  cstr_ok tfibsegs (cx_W0 cx) (cx_mem cx) (cx_lp cx) (cx_lb cx) /\
  cstr_kept B (cx_ly cx) (cx_S cx) (cx_t cx) (cx_tb cx) /\
  cstr_kept B (cx_ly cx) (cx_S cx) (cx_lp cx) (cx_lb cx) /\
  cx_lb cx <> [] /\ 0 <= cx_q cx /\ 0 <= cx_plen cx /\ cx_q cx + cx_plen cx <= Z.of_nat (length (cx_tb cx)) /\
  Z.of_nat (length (cx_tb cx)) <= MANIFEST_MAX /\
  arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H (cx_W0 cx)) (cx_mem cx)).
(* the state at a program point of the loop, with at = t + a an occurrence of the location *)
Definition hp_st (cx : hpcx) (a : nat) (lyc : alayout) (Sc : astate) (W : world tfibsegs) (regs : bvmap 5 word)
  (m : word -> option byte) (mdc : Model) : Prop :=
  hp_entry_ok cx /\
  ajournal tfibsegs B STK_has_prefixed (spZ (cx_regs0 cx)) [] (cx_ly cx) (cx_S cx) (cx_W0 cx) (cx_mem cx) (cx_md cx)
    [] lyc Sc W m mdc 0 /\
  ablocks B lyc Sc = ablocks B (cx_ly cx) (cx_S cx) /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\ spZ regs = spZ (cx_regs0 cx) - 112 /\
  hp_frame W (cx_regs0 cx) m /\
  getr regs 8 = w64 (cx_lp cx) /\ getr regs 9 = w64 (cx_plen cx) /\ getr regs 18 = w64 (cx_t cx + cx_q cx) /\
  getr regs 19 = w64 (cx_t cx) /\ getr regs 20 = w64 (Z.of_nat (length (cx_lb cx))) /\
  getr regs 21 = w64 (cx_t cx + Z.of_nat a) /\ getr regs 23 = w64 SBz /\ getr regs 24 = w64 (cx_plen cx + 1) /\
  getr regs 26 = w64 58 /\ getr regs 27 = Z_to_bv 64 (- cx_plen cx) /\
  has_prefixed_model.mt (cx_tb cx) (cx_lb cx) a = true /\
  fm_glob tfibsegs W m (cx_live cx) (cx_peak cx) (cx_cnt cx) (cx_fail cx).
(* the walk from pc reaches has_prefixed's post from every loop state at a that satisfies P *)
Definition hp_cont (cx : hpcx) (pc : Z) (a : nat) (P : bvmap 5 word -> Prop) : Prop :=
  forall lyc Sc W regs m mdc, hp_st cx a lyc Sc W regs m mdc -> P regs ->
  SRr tfibsegs W (cfg_at tfibsegs pc regs m mdc) (hp_post cx).

(* start = a - plen - 1 is the candidate token index; s6 = t + start, s9 = t + start + 1 *)
Definition hp_s69 (cx : hpcx) (a : nat) (regs : bvmap 5 word) : Prop :=
  (Z.to_nat (cx_plen cx) + 1 <= a)%nat /\
  getr regs 22 = w64 (cx_t cx + Z.of_nat a - cx_plen cx - 1) /\ getr regs 25 = w64 (cx_t cx + Z.of_nat a - cx_plen cx).

(* ---- the five loop segments (lv2_locate.c:63-75); each ends in the loop tail or the next segment ---- *)
(* 0x821b0..0x821d8: a < plen + 1, or check at[-1] (0x821c4..0x821d0, report 0x822c0) and at[-1] <> ':' -> tail *)
Definition seg_head_ok : Prop := forall cx a,
  hp_cont cx HP_TAIL a (fun _ => (a < Z.to_nat (cx_plen cx) + 1)%nat \/
                                 ManifestModel.byte_at (cx_tb cx) (a - 1) <> 58) ->
  hp_cont cx HP_NCMP a (fun r => hp_s69 cx a r /\ ManifestModel.byte_at (cx_tb cx) (a - 1) = 58) ->
  hp_cont cx HP_HEAD a (fun _ => True).
(* 0x821dc..0x821ec: strncmp (t + start, t + q, plen) <> 0 -> tail *)
Definition seg_ncmp_ok : Prop := forall cx a,
  hp_cont cx HP_TAIL a (fun _ => ~ strn_eq (Z.to_nat (cx_plen cx))
                                     (skipn (a - Z.to_nat (cx_plen cx) - 1) (cx_tb cx))
                                     (skipn (Z.to_nat (cx_q cx)) (cx_tb cx))) ->
  hp_cont cx HP_PRE a (fun r => hp_s69 cx a r /\ strn_eq (Z.to_nat (cx_plen cx))
                                     (skipn (a - Z.to_nat (cx_plen cx) - 1) (cx_tb cx))
                                     (skipn (Z.to_nat (cx_q cx)) (cx_tb cx))) ->
  hp_cont cx HP_NCMP a (hp_s69 cx a).
(* 0x821f0..0x8221c: start = 0 -> post; else check start[-1] (0x821f8..0x82204, report 0x82278), c = start[-1],
   name_char (c) (0x82210); c = '.' or name_char c -> tail, else post *)
Definition seg_pre_ok : Prop := forall cx a,
  hp_cont cx HP_TAIL a (fun _ => (0 < a - Z.to_nat (cx_plen cx) - 1)%nat /\
    (ManifestModel.byte_at (cx_tb cx) (a - Z.to_nat (cx_plen cx) - 2) = 46 \/
     ManifestModel.name_char (ManifestModel.byte_at (cx_tb cx) (a - Z.to_nat (cx_plen cx) - 2)) = true)) ->
  hp_cont cx HP_POST a (fun _ => (a - Z.to_nat (cx_plen cx) - 1)%nat = O \/
    ((0 < a - Z.to_nat (cx_plen cx) - 1)%nat /\
     ManifestModel.byte_at (cx_tb cx) (a - Z.to_nat (cx_plen cx) - 2) <> 46 /\
     ManifestModel.name_char (ManifestModel.byte_at (cx_tb cx) (a - Z.to_nat (cx_plen cx) - 2)) = false)) ->
  hp_cont cx HP_PRE a (hp_s69 cx a).
(* 0x82220..0x8223c: check at[|lb|] (0x82224..0x82230, report 0x822bc), name_char (at[|lb|]) (0x82238); 0 -> return 1
   (0x8227c), else tail *)
Definition seg_post_ok : Prop := forall cx a,
  (ManifestModel.name_char (ManifestModel.byte_at (cx_tb cx) (a + length (cx_lb cx))) = false -> hp_res cx = 1) ->
  hp_cont cx HP_TAIL a (fun _ =>
    ManifestModel.name_char (ManifestModel.byte_at (cx_tb cx) (a + length (cx_lb cx))) = true) ->
  hp_cont cx HP_POST a (fun _ => True).
(* 0x82240..0x82254: at = strstr (at + 1, location) (0x82248); a hit -> loop head, NULL -> return 0 *)
Definition seg_tail_ok : Prop := forall cx a,
  (no_occ (skipn (S a) (cx_tb cx)) (cx_lb cx) -> hp_res cx = 0) ->
  (forall j, first_occ (skipn (S a) (cx_tb cx)) (cx_lb cx) j -> hp_cont cx HP_HEAD (S a + j) (fun _ => True)) ->
  hp_cont cx HP_TAIL a (fun _ => True).

(* ======== lemmas the segments use ======== *)

Lemma hp_st_static : forall cx a lyc Sc W regs m mdc, hp_st cx a lyc Sc W regs m mdc ->
  astk_ok STK_has_prefixed (cx_ly cx) (spZ (cx_regs0 cx)) /\ AR tfibsegs B lyc Sc W m mdc.
Proof.
intros cx a lyc Sc W regs m mdc (_ & HJ & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _). split; assumption.
Qed.

(* the relro view and the C strings at any state of the walk: the strings live in live blocks the walk keeps or in
   fm's read-only strings (cstr_kept), so the walk's journal (footprint []) keeps them, as G5's FMW_kitS.v
   cstr_ok_kept *)
Lemma hp_aro : forall cx a lyc Sc W regs m mdc, hp_st cx a lyc Sc W regs m mdc ->
  arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W) m).
Proof.
intros cx a lyc Sc W regs m mdc (HE & HJ & _). pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO).
apply (arodata_journal tfibsegs B FM_RLO FM_RHI _ _ [] _ _ _ _ _ [] lyc Sc W m mdc 0 HJ
  (fun a => fp_spares_closed [] a sink_closed_nil) inFP_nil g2_relro_img HRO).
Qed.
Lemma hp_rom : forall cx a lyc Sc W regs m mdc, hp_st cx a lyc Sc W regs m mdc ->
  rom_viewN tfibsegs B W m /\ rom_viewO tfibsegs B W m.
Proof.
intros cx a lyc Sc W regs m mdc H. pose proof (hp_aro cx a lyc Sc W regs m mdc H) as HRO.
pose proof (proj2 (hp_st_static cx a lyc Sc W regs m mdc H)) as HAR.
destruct (IMGF lyc Sc W m mdc HAR HRO) as (H1 & H2 & _). split; assumption.
Qed.

(* a live heap block is visible from its start to the end of the 8-byte word holding its last byte (as G6's FMW_kit.v
   block_word_tail_vis) *)
Lemma g2_word_end_le : forall x base ext, base mod 16 = 0 -> ext mod 8 = 0 -> x < base + ext ->
  x - x mod 8 + 8 <= base + ext.
Proof.
intros x base ext H1 H2 H3.
pose proof (Z.div_mod base 16 ltac:(lia)) as D1. pose proof (Z.div_mod ext 8 ltac:(lia)) as D2.
pose proof (Z.div_mod x 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as D4.
lia.
Qed.
Lemma g2_extent_mod8 : forall k, 0 <= ck_req k -> ck_extent k mod 8 = 0.
Proof.
intros k Hq. unfold ck_extent. destruct (from_primary (ck_req k)) eqn:Ep.
- pose proof (primary_geometry (ck_req k) Hq Ep) as (_ & _ & _ & H32 & _).
  set (c := class_size (chunk_class (ck_req k))) in *.
  pose proof (Z.div_mod c 32 ltac:(lia)) as D. pose proof (Z.div_mod c 8 ltac:(lia)) as D8.
  pose proof (Z.mod_pos_bound c 8 ltac:(lia)) as R8. lia.
- pose proof (secondary_geometry (ck_req k) Hq Ep) as (_ & _ & _ & _ & HP & _).
  set (s := sec_map_size (ck_req k)) in *. unfold kPage in *.
  pose proof (Z.div_mod s 4096 ltac:(lia)) as D. pose proof (Z.div_mod (s - 4096) 8 ltac:(lia)) as D8.
  pose proof (Z.mod_pos_bound (s - 4096) 8 ltac:(lia)) as R8. lia.
Qed.
Lemma g2_block_tail_vis : forall ly S (W : world tfibsegs) mem md b m,
  AR tfibsegs B ly S W mem md -> In (b, m) (ablocks B ly S) -> 0 < m ->
  forall a, b <= a < (b + m - 1) - (b + m - 1) mod 8 + 8 -> aview tfibsegs (w_H W) mem a <> None.
Proof.
intros ly S W mem md b m HAR Hin Hm a Ha.
assert (Hrq : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
destruct (Z_lt_le_dec a (b + m)) as [Hlt | Hge].
- destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & _ & _ & _ & Hpres & _).
  apply (aview_some_of_apresent tfibsegs). exact (proj1 (Hpres a ltac:(lia))).
- destruct HAR as (M & _).
  apply In_ablocks in Hin as (k & Hk & Hst & Hu & Hn).
  pose proof (chunk_facts B ly S _ k M Hk) as (_ & _ & Hb16 & Huser & _ & _ & Hreq & Hext & _).
  rewrite Hn, Hrq in Hext.
  assert (Hcn : ck_n k = m) by (unfold ck_n; rewrite Hn; exact Hrq).
  pose proof (g2_extent_mod8 k ltac:(lia)) as Hx8.
  pose proof (g2_word_end_le (b + m - 1) (ck_base B ly k) (ck_extent k) Hb16 Hx8 ltac:(lia)) as Hend.
  pose proof (am_junk B ly S _ M) as HJ. rewrite Forall_forall in HJ.
  specialize (HJ (aoff (sptr_exp (ck_beg k)) (ck_rz k + ck_n k), ck_extent k - ck_rz k - ck_n k)).
  unfold range_vis in HJ. cbn [fst snd] in HJ.
  assert (NSH : forall e', sptr_exp (ck_beg k) <> ASh e') by (intros e'; destruct (ck_beg k); cbn; discriminate).
  rewrite (aeval_aoff B ly (sptr_exp (ck_beg k)) (ck_rz k + ck_n k) NSH) in HJ.
  assert (Eb : aeval B ly (sptr_exp (ck_beg k)) = ck_base B ly k) by reflexivity.
  replace a with (aeval B ly (sptr_exp (ck_beg k)) + (ck_rz k + ck_n k) + (a - (b + m))) by lia.
  apply HJ; [|lia].
  unfold ajunk. apply in_cons. apply in_cons.
  apply in_or_app; right. apply in_or_app; right. apply in_or_app; left.
  apply in_flat_map. exists k. split; [exact Hk|].
  unfold chunk_junk. cbv zeta.
  apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. apply in_eq.
Qed.
Lemma g2_word_end_mono : forall x y, x <= y -> x - x mod 8 + 8 <= y - y mod 8 + 8.
Proof.
intros x y H. pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.div_mod y 8 ltac:(lia)) as Dy.
pose proof (Z.mod_pos_bound x 8 ltac:(lia)). pose proof (Z.mod_pos_bound y 8 ltac:(lia)).
assert (x / 8 <= y / 8) by (apply Z.div_le_mono; lia). lia.
Qed.
(* a C string in a live block, carried over a journal with footprint [] that keeps the block (G5's cstr_ok_kept_blk) *)
Lemma g2_cstr_kept_blk : forall STK sp0 ly S W mem md own ly' S' W' mem' md' k p l b m,
  ajournal tfibsegs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  In (b, m) (ablocks B ly S) -> In (b, m) (ablocks B ly' S') -> b <= p -> p + Z.of_nat (length l) + 1 <= b + m ->
  cstr_ok tfibsegs W mem p l -> cstr_ok tfibsegs W' mem' p l.
Proof.
intros STK sp0 ly S W mem md own ly' S' W' mem' md' k p l b m HJ Hin Hin' Hb Hbm
  ((Hg & Hnz) & H4096 & Hcl & H32 & Ham & Hra & Hhv & Htl).
pose proof HJ as (HAR' & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
assert (Hm : 0 < m) by lia.
assert (Hrq : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
split; [split; [|exact Hnz]|].
{ apply (garr8_frame tfibsegs _ _ p (l ++ [0]) Hg). intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
  apply (mbyte_of_aview tfibsegs). replace a with (b + (a - b)) by lia.
  apply (F2 b m (a - b) Hin Hin'); [rewrite Hrq; lia | replace (b + (a - b)) with a by lia; apply inFP_nil]. }
split; [exact H4096|]. split; [exact Hcl|]. split; [exact H32|]. split; [exact Ham|].
split.
{ apply (range_addressable_of_block tfibsegs B LAWS ly' S' W' mem' md' b m p _ HAR' Hin' Hb). rewrite Hrq. lia. }
split.
{ destruct (al_shadow _ _ LAWS ly' S' W' mem' md' b m HAR' Hin') as (_ & Hhv').
  apply (g2_hull_sub _ b (req_size m) p _ Hhv' Hb); rewrite ?Hrq; lia. }
intros a Ha. apply (g2_block_tail_vis ly' S' W' mem' md' b m HAR' Hin' Hm).
pose proof (g2_word_end_mono (p + Z.of_nat (length l)) (b + m - 1) ltac:(lia)). lia.
Qed.
(* the two strings at any loop state *)
Lemma hp_cstr : forall cx a lyc Sc W regs m mdc, hp_st cx a lyc Sc W regs m mdc ->
  cstr_ok tfibsegs W m (cx_t cx) (cx_tb cx) /\ cstr_ok tfibsegs W m (cx_lp cx) (cx_lb cx).
Proof.
intros cx a lyc Sc W regs m mdc H.
pose proof (hp_aro cx a lyc Sc W regs m mdc H) as HRO.
destruct H as (HE & HJ & Hab & _).
pose proof HE as (_ & _ & _ & Ht & Hl & Hkt & Hkl & _).
pose proof HJ as (HAR & _).
assert (KEEP : forall p l, cstr_kept B (cx_ly cx) (cx_S cx) p l ->
  cstr_ok tfibsegs (cx_W0 cx) (cx_mem cx) p l -> cstr_ok tfibsegs W m p l).
{ intros p l [(b & n & Hin & Hb & Hbn) | (p0 & l0 & k & Hsrc & Hkl0 & -> & ->)] Hc.
  - apply (g2_cstr_kept_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ p l b n HJ Hin); [rewrite Hab; exact Hin | exact Hb | exact Hbn | exact Hc].
  - apply (g2_cstr_suffix W m p0 l0 k Hkl0).
    destruct Hsrc as [Hro | (ps & Hf & ->)].
    + destruct (IMGF lyc Sc W m mdc HAR HRO) as (_ & _ & _ & HS & _).
      exact (proj1 (proj1 (Forall_forall _ _) HS (p0, l0) Hro)).
    + destruct (IMGF lyc Sc W m mdc HAR HRO) as (_ & _ & _ & _ & HF). exact (proj1 (HF p0 ps Hf)). }
split; [exact (KEEP _ _ Hkt Ht) | exact (KEEP _ _ Hkl Hl)].
Qed.
(* the bytes of the text at any loop state *)
Lemma hp_tbyte : forall cx a lyc Sc W regs m mdc i, hp_st cx a lyc Sc W regs m mdc -> (i <= length (cx_tb cx))%nat ->
  val_mem tfibsegs (mrestrict (w_H W) m) (cx_t cx + Z.of_nat i) 1 (ManifestModel.byte_at (cx_tb cx) i) /\
  0 <= ManifestModel.byte_at (cx_tb cx) i < 256.
Proof.
intros cx a lyc Sc W regs m mdc i H Hi. destruct (hp_cstr cx a lyc Sc W regs m mdc H) as ((Hc & _) & _).
exact (cstr_byte W m _ _ i Hc Hi).
Qed.

(* ---- seats ---- *)
Lemma hp_sp : forall cx a lyc Sc W regs m mdc, hp_st cx a lyc Sc W regs m mdc ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 /\ spZ regs mod 16 = 0 /\ alloc_ceiling + 8192 <= spZ regs.
Proof.
intros cx a lyc Sc W regs m mdc H. pose proof (hp_st_static cx a lyc Sc W regs m mdc H) as (Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct H as (_ & _ & _ & _ & _ & Hsp & _). rewrite Hsp. ceil2.
assert (FFS : STK_has_prefixed = 8304) by reflexivity. rewrite FFS in *.
split; [lia|]. split; [|lia]. rewrite Zminus_mod, Hal16. reflexivity.
Qed.
Lemma hp_seat : forall cx a lyc Sc W regs m mdc pc, hp_st cx a lyc Sc W regs m mdc ->
  st_ok tfibsegs (Ereg regs []) (ss_hs pc) (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) m (seg_rom tfibsegs))).
Proof.
intros cx a lyc Sc W regs m mdc pc H. pose proof (hp_sp cx a lyc Sc W regs m mdc H) as (Hsp1 & Hsp2 & _).
pose proof H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q23 & _).
assert (E2 : ew (Ereg regs []) 2 = getr regs 2) by exact (ew_Ereg_nat regs _ 2 2%bv eq_refl).
assert (E23 : ew (Ereg regs []) 23 = getr regs 23) by exact (ew_Ereg_nat regs _ 23 23%bv eq_refl).
rewrite restrict_mkst_fx. unfold ss_hs. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- exact I.
- split; [|split; exact I]. cbn [hs_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2, E23, Q23. change (2 ^ 4) with 16. unfold w64, SBz. rewrite unsigned_lit_small by lia.
  rewrite Z.pow_0_r, Z.mod_1_r. unfold spZ in *. repeat split; lia.
Qed.
Lemma hp_seat_chk : forall cx a lyc Sc W regs m mdc pc x c, hp_st cx a lyc Sc W regs m mdc ->
  getr regs 10 = w64 x -> 4096 <= x <= 2 ^ 47 - 8 ->
  val_mem tfibsegs (mrestrict (w_H W) m) x 1 c -> 0 <= c < 256 ->
  st_ok tfibsegs (Ereg regs [w64 c]) (ss_hc pc) (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) m (seg_rom tfibsegs))).
Proof.
intros cx a lyc Sc W regs m mdc pc x c H H10 Hx Hv Hc. pose proof (hp_sp cx a lyc Sc W regs m mdc H) as (Hsp1 & Hsp2 & _).
pose proof H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q23 & _).
set (E := Ereg regs [w64 c]).
assert (E2 : ew E 2 = getr regs 2) by exact (ew_Ereg_nat regs _ 2 2%bv eq_refl).
assert (E10 : ew E 10 = getr regs 10) by exact (ew_Ereg_nat regs _ 10 10%bv eq_refl).
assert (E23 : ew E 23 = getr regs 23) by exact (ew_Ereg_nat regs _ 23 23%bv eq_refl).
assert (E32 : ew E 32 = w64 c) by exact (ew_Ereg_extra regs _ 0).
assert (U10 : bv_unsigned (ew E 10) = x) by (rewrite E10, H10; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold ss_hc. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold hc_region, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. fold E. rewrite U10.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val tfibsegs E _ x 0 1 (SOff 32 0) c);
    [cbn [sv_denot]; rewrite E32; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Hv].
- cbn. tauto.
- split; [|split; exact I]. cbn [hc_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite E2, E23, Q23, U10. change (2 ^ 4) with 16. unfold w64, SBz. rewrite unsigned_lit_small by lia.
  rewrite Z.pow_0_r, Z.mod_1_r. unfold spZ in *. repeat split; lia.
Qed.
(* the shadow entry of a checked byte of the text (indices 0 .. |tb|, the NUL included) *)
Lemma hp_shok : forall cx a lyc Sc W regs m mdc c i, hp_st cx a lyc Sc W regs m mdc ->
  getr regs 10 = w64 (cx_t cx + Z.of_nat i) -> (i <= length (cx_tb cx))%nat ->
  sh_ok tfibsegs hc_Bx hc_SH (Ereg regs [w64 c]) (mrestrict (w_H W) m).
Proof.
intros cx a lyc Sc W regs m mdc c i H H10 Hi.
pose proof (hp_cstr cx a lyc Sc W regs m mdc H) as (Ht & _).
pose proof Ht as (_ & H4096 & Hcl & _ & _ & Hra & _).
pose proof H as (HE & HJ & Hab & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q23 & _).
pose proof HE as (_ & _ & _ & _ & _ & Hkt & _).
pose proof HJ as (HAR & _).
ceil2.
set (E := Ereg regs [w64 c]).
assert (UB : U E hc_Bx = SHADOW_OFF).
{ unfold hc_Bx. apply (U_atom E 23 SBz); [unfold E; rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl), Q23; reflexivity | unfold SBz; lia]. }
assert (U10 : U E (SOff 10 0) = cx_t cx + Z.of_nat i).
{ apply (U_atom E 10); [unfold E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10; reflexivity | lia]. }
apply Forall_cons; [|apply Forall_nil].
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite UB, U10. rewrite <- (aview_rd_of tfibsegs).
split.
- eapply range_addressable_sub; [exact Hra | lia | lia].
- rewrite Z.min_l, Z.max_r by lia. rewrite Z.add_0_r. intros x Hx.
  destruct Hkt as [(b & n & Hin & Hb & Hbn) | (p0 & l0 & k & Hsrc & Hkl0 & Ep & El)].
  + rewrite <- Hab in Hin.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & _ & _ & Happ & _).
    assert (Hrq : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
    rewrite Hrq in Happ. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
  + assert (Hlo : p0 + Z.of_nat (length l0) < 0x30000).
    { destruct Hsrc as [Hro | (ps & Hf & ->)].
      - cbv [FM_RO_STRS In STR_empty] in Hro.
        repeat (destruct Hro as [Hro | Hro]; [injection Hro as <- <-; cbn; lia |]). destruct Hro.
      - cbv [FM_SN_FMTS In FMT_whole FMT_tw FMT_tx FMT_t1 FMT_t2 FMT_t3 FMT_t1x] in Hf.
        repeat (destruct Hf as [Hf | Hf]; [injection Hf as <- <-; vm_compute; reflexivity |]). destruct Hf. }
    rewrite El, length_skipn in Hi. rewrite Ep in Hx.
    unfold SHADOW_OFF in *. lia.
Qed.

(* ---- moving the loop state ---- *)
Lemma hp_frame_gframe : forall W regs m m' lo hi,
  gframe tfibsegs W lo hi m m' -> hi <= spZ regs - 104 -> 0 <= spZ regs - 104 -> spZ regs <= 2 ^ 64 ->
  hp_frame W regs m -> hp_frame W regs m'.
Proof.
intros W regs m m' lo hi HG Hhi Hp Hsp (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13).
repeat split;
  solve [ eapply (val_mem_gframe_hi tfibsegs W lo hi m m'); [exact HG | lia | lia | cbn; lia |];
          first [exact K1|exact K2|exact K3|exact K4|exact K5|exact K6|exact K7|exact K8|exact K9|exact K10
                |exact K11|exact K12|exact K13] ].
Qed.
(* a step that writes nothing outside [sp0 - 8304, sp0 - 104) and keeps HP_KEEP; s5 may move to another occurrence *)
Lemma hp_st_move : forall cx a a' lyc Sc W regs m mdc regs' m' mdc',
  hp_st cx a lyc Sc W regs m mdc ->
  ajournal tfibsegs B STK_has_prefixed (spZ (cx_regs0 cx)) [] (cx_ly cx) (cx_S cx) (cx_W0 cx) (cx_mem cx) (cx_md cx)
    [] lyc Sc W m' mdc' 0 ->
  gframe tfibsegs W (spZ (cx_regs0 cx) - STK_has_prefixed) (spZ (cx_regs0 cx) - 104) m m' ->
  regs_keep HP_KEEP regs regs' ->
  getr regs' 21 = w64 (cx_t cx + Z.of_nat a') -> has_prefixed_model.mt (cx_tb cx) (cx_lb cx) a' = true ->
  hp_st cx a' lyc Sc W regs' m' mdc'.
Proof.
intros cx a a' lyc Sc W regs m mdc regs' m' mdc' H HJ' HG HK Q21 Hmt.
pose proof (hp_st_static cx a lyc Sc W regs m mdc H) as (Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (FFS : STK_has_prefixed = 8304) by reflexivity.
destruct H as (HE & _ & Hab & Q3 & Q4 & Hsp & HF & Q8 & Q9 & Q18 & Q19 & Q20 & _ & Q23 & Q24 & Q26 & Q27 & _ & Hgl).
assert (K : forall r, In r HP_KEEP -> getr regs' r = getr regs r) by exact HK.
split; [exact HE|]. split; [exact HJ'|]. split; [exact Hab|].
split; [rewrite K by (cbv; tauto); exact Q3|]. split; [rewrite K by (cbv; tauto); exact Q4|].
split; [unfold spZ; rewrite K by (cbv; tauto); exact Hsp|].
ceil2.
split; [apply (hp_frame_gframe W (cx_regs0 cx) m m' _ _ HG); [lia | rewrite FFS in *; lia | lia | exact HF]|].
split; [rewrite K by (cbv; tauto); exact Q8|]. split; [rewrite K by (cbv; tauto); exact Q9|].
split; [rewrite K by (cbv; tauto); exact Q18|]. split; [rewrite K by (cbv; tauto); exact Q19|].
split; [rewrite K by (cbv; tauto); exact Q20|]. split; [exact Q21|].
split; [rewrite K by (cbv; tauto); exact Q23|]. split; [rewrite K by (cbv; tauto); exact Q24|].
split; [rewrite K by (cbv; tauto); exact Q26|]. split; [rewrite K by (cbv; tauto); exact Q27|].
split; [exact Hmt|].
apply (fm_glob_gframe tfibsegs W _ _ m m' _ _ _ _ HG); [rewrite FFS; lia | exact Hgl].
Qed.

(* a call to a runtime routine in FMH_Rt's rt_post_ro form from a loop state, its sp = sp0 - 112 *)
Lemma hp_call_rt : forall cx a lyc Sc W regs m mdc (STKr pc ret : Z) (R : Z -> Prop),
  hp_st cx a lyc Sc W regs m mdc -> ESTACK <= STKr <= 8192 ->
  getr regs 1 = Z_to_bv 64 ret -> 0 <= ret < 2 ^ 64 -> ret mod 2 = 0 ->
  (ecall_pre_k tfibsegs B STKr lyc Sc W regs m mdc ->
     SRr tfibsegs W (cfg_at tfibsegs pc regs m mdc) (rt_post_ro tfibsegs B STKr lyc Sc W regs m mdc R)) ->
  (forall regs2 m2 md2 v, hp_st cx a lyc Sc W regs2 m2 md2 -> aregs_preserved regs regs2 ->
     getr regs2 10 = w64 v -> 0 <= v < 2 ^ 64 -> R v ->
     SRr tfibsegs W (cfg_at tfibsegs ret regs2 m2 md2) (hp_post cx)) ->
  SRr tfibsegs W (cfg_at tfibsegs pc regs m mdc) (hp_post cx).
Proof.
intros cx a lyc Sc W regs m mdc STKr pc ret R H HST Hra Hret Hev HC K.
pose proof (hp_sp cx a lyc Sc W regs m mdc H) as (Hsp1 & Hsp2 & _).
pose proof H as (HE & HJ & _ & Q3 & Q4 & Hsp & _).
pose proof HE as (_ & G3 & G4 & _).
pose proof (hp_st_static cx a lyc Sc W regs m mdc H) as (Hstk & _).
pose proof Hstk as (Hal16 & _).
assert (FFS : STK_has_prefixed = 8304) by reflexivity.
assert (Rret : YK0s.ret_ok (getr regs 1)) by (rewrite Hra; apply g2_ret_ok_lit; lia).
eapply SRr_bind.
{ unfold cfg_at. apply (aj_rt_ro tfibsegs B LAWS g2_segs_low STKr pc R W regs m STK_has_prefixed (spZ (cx_regs0 cx))
    [] _ _ _ _ _ [] lyc Sc mdc 0 (-112) (getr regs 1) HJ).
  - exact Hsp.
  - reflexivity.
  - lia.
  - lia.
  - rewrite FFS; lia.
  - exact Q3.
  - exact Q4.
  - reflexivity.
  - exact Rret.
  - exact HC. }
cbv beta. intros W2 c2 _ (-> & regs2 & m2 & md2 & v & -> & HJ2 & HP2 & Ha0 & Hv & HRv & G2 & _).
replace (getr regs 1) with (w64 ret) by (rewrite Hra; reflexivity). fold (cfg_at tfibsegs ret regs2 m2 md2).
apply (K regs2 m2 md2 v); [| exact HP2 | exact Ha0 | exact Hv | exact HRv].
apply (hp_st_move cx a a lyc Sc W regs m mdc regs2 m2 md2 H HJ2).
- apply (gframe_widen tfibsegs W _ _ (spZ (cx_regs0 cx) + -112 - STKr) (spZ (cx_regs0 cx) + -112)); [exact G2 | |];
    rewrite ?FFS; lia.
- apply regs_keep_of_preserved. exact HP2.
- pose proof H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q21 & _).
  rewrite <- Q21. replace (21%bv : bv 5) with (Z_to_bv 5 21) by (apply bv_eq; reflexivity).
  apply HP2. unfold acallee_saved. lia.
- pose proof H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmt & _). exact Hmt.
Qed.

(* a call to name_char from a loop state (name_char_holds, FMW_name_char.v) *)
Hypothesis AISALNUM : aisalnum_realizes tfibsegs B PC_isalnum.
Lemma hp_call_nc : forall cx a lyc Sc W regs m mdc (ret c : Z),
  hp_st cx a lyc Sc W regs m mdc ->
  getr regs 1 = Z_to_bv 64 ret -> 4096 <= ret < 2 ^ 64 -> ret mod 2 = 0 ->
  getr regs 10 = w64 c -> 0 <= c < 256 ->
  (forall ly2 S2 W2 regs2 m2 md2, hp_st cx a ly2 S2 W2 regs2 m2 md2 -> aregs_preserved regs regs2 ->
     getr regs2 10 = w64 (if ManifestModel.name_char c then 1 else 0) ->
     SRr tfibsegs W2 (cfg_at tfibsegs ret regs2 m2 md2) (hp_post cx)) ->
  SRr tfibsegs W (cfg_at tfibsegs A_name_char regs m mdc) (hp_post cx).
Proof.
intros cx a lyc Sc W regs m mdc ret c H Hra Hret Hev H10 Hc K.
pose proof (hp_sp cx a lyc Sc W regs m mdc H) as (Hsp1 & Hsp2 & Hspc).
pose proof (hp_aro cx a lyc Sc W regs m mdc H) as HRO.
pose proof H as (HE & HJ & Hab & Q3 & Q4 & Hsp & HF & Q8 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgl).
pose proof (hp_st_static cx a lyc Sc W regs m mdc H) as (Hstk & HAR).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (FFS : STK_has_prefixed = 8304) by reflexivity. assert (FNC : STK_name_char = 4112) by reflexivity.
pose proof (hp_cstr cx a lyc Sc W regs m mdc H) as (_ & Hl). pose proof Hl as (_ & Hl4 & Hlcl & _).
ceil2.
assert (Rret : YK0s.ret_ok (getr regs 1)) by (rewrite Hra; apply g2_ret_ok_lit; lia).
assert (HPRE : afn_pre tfibsegs B STK_name_char lyc Sc W regs m mdc []).
{ apply (afn_pre_at tfibsegs B STK_has_prefixed (spZ (cx_regs0 cx)) [] _ _ _ _ _ [] lyc Sc W m mdc 0 regs
    STK_name_char (-112) [] HJ); try lia.
  - exact Rret.
  - unfold raZ. rewrite Hra. rewrite unsigned_lit_small by lia. lia.
  - exact Q3.
  - exact Q4.
  - apply achain_low. unfold s0Z. rewrite Q8. unfold w64. rewrite unsigned_lit_small by lia. lia. }
eapply SRr_bind.
{ apply (name_char_holds B LAWS AISALNUM lyc Sc W regs m mdc [] c (cx_live cx) (cx_peak cx) (cx_cnt cx) (cx_fail cx));
    [split; [exact HPRE | exact HRO] | exact Hgl | exact H10 | exact Hc]. }
unfold fpost, apost_base. cbv beta.
intros W2 c2 _ (ly2 & S2 & regs2 & m2 & md2 & -> & HJ1 & HP2 & Ha0 & Hab2 & Hgl2).
replace (getr regs 1) with (w64 ret) by (rewrite Hra; reflexivity). fold (cfg_at tfibsegs ret regs2 m2 md2).
apply (K ly2 S2 W2 regs2 m2 md2); [| exact HP2 | exact Ha0].
assert (HJ2 : ajournal tfibsegs B STK_has_prefixed (spZ (cx_regs0 cx)) [] (cx_ly cx) (cx_S cx) (cx_W0 cx) (cx_mem cx)
  (cx_md cx) [] ly2 S2 W2 m2 md2 0).
{ pose proof (ajournal_sub tfibsegs B LAWS g2_segs_low STK_has_prefixed (spZ (cx_regs0 cx)) [] (cx_ly cx) (cx_S cx)
    (cx_W0 cx) (cx_mem cx) (cx_md cx) [] lyc Sc W m mdc 0 STK_name_char (spZ regs) [] [] ly2 S2 W2 m2 md2 0 HJ HJ1
    ltac:(rewrite Hsp, FFS, FNC; lia) ltac:(lia) ltac:(intros x Hx; exfalso; exact (inFP_nil x Hx))) as X.
  exact X. }
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _).
assert (KP : regs_keep HP_KEEP regs regs2) by (apply regs_keep_of_preserved; exact HP2).
assert (KR : forall r, In r HP_KEEP -> getr regs2 r = getr regs r) by exact KP.
destruct H as (_ & _ & _ & _ & _ & _ & _ & R8 & R9 & R18 & R19 & R20 & R21 & R23 & R24 & R26 & R27 & Hmt & _).
split; [exact HE|]. split; [exact HJ2|]. split; [rewrite Hab2; exact Hab|].
split; [rewrite KR by (cbv; tauto); exact Q3|]. split; [rewrite KR by (cbv; tauto); exact Q4|].
split; [unfold spZ; rewrite KR by (cbv; tauto); exact Hsp|].
split.
{ pose proof HF as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13).
  assert (FR : forall p n v, spZ (cx_regs0 cx) - 104 <= p -> p + Z.of_nat n <= spZ (cx_regs0 cx) ->
    val_mem tfibsegs (mrestrict (w_H W) m) p n v -> val_mem tfibsegs (mrestrict (w_H W2) m2) p n v).
  { intros p n v Hp Hpn Hv kk Hkk. rewrite <- (Hv kk Hkk). apply (mbyte_of_aview tfibsegs). apply G1; lia. }
  repeat split; (apply FR; [cbn; lia | cbn; lia |]); assumption. }
split; [rewrite KR by (cbv; tauto); exact R8|]. split; [rewrite KR by (cbv; tauto); exact R9|].
split; [rewrite KR by (cbv; tauto); exact R18|]. split; [rewrite KR by (cbv; tauto); exact R19|].
split; [rewrite KR by (cbv; tauto); exact R20|].
split; [rewrite <- R21; replace (21%bv : bv 5) with (Z_to_bv 5 21) by (apply bv_eq; reflexivity);
        apply HP2; unfold acallee_saved; lia|].
split; [rewrite KR by (cbv; tauto); exact R23|]. split; [rewrite KR by (cbv; tauto); exact R24|].
split; [rewrite KR by (cbv; tauto); exact R26|]. split; [rewrite KR by (cbv; tauto); exact R27|].
split; [exact Hmt | exact Hgl2].
Qed.

(* the strstr contract with no user-poisoned range, in rt_post_ro form *)
Lemma hp_strstr_ro : astrstr_realizes tfibsegs B PC_strstr -> forall ly S W regs mem md x y (lt lw : list Z),
  ecall_pre_k tfibsegs B STK_RT_STRSTR ly S W regs mem md -> rom_viewN tfibsegs B W mem -> rom_viewO tfibsegs B W mem ->
  getr regs 10 = w64 x -> getr regs 11 = w64 y ->
  cstr_ok tfibsegs W mem x lt -> cstr_ok tfibsegs W mem y lw ->
  SRr tfibsegs W (cfg_at tfibsegs PC_strstr regs mem md)
    (rt_post_ro tfibsegs B STK_RT_STRSTR ly S W regs mem md
      (fun v => (v = 0 /\ no_occ lt lw) \/ (exists j, first_occ lt lw j /\ v = x + Z.of_nat j))).
Proof.
intros ASTRSTR ly S W regs mem md x y lt lw (HP & Hceil & Hlo & Hpr) HN HO G10 G11 Hx Hy.
eapply SRr_mono.
- apply (ASTRSTR ly S [] W regs mem md x y lt lw); try assumption.
  split; [apply ecall_preU_nil; exact HP|]. split; [exact Hceil|]. split; [exact Hlo | exact Hpr].
- cbv beta. intros W' c' _ Hpost. exact (rt_post_ro_of_roU tfibsegs B STK_RT_STRSTR ly S W regs mem md _ W' c' Hpost).
Qed.

Lemma hp_loop_entry : forall (pc : Z) ly' S' (W : world tfibsegs) (regs' : bvmap 5 word) mem' md' sp0
  (ra0 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : Z),
  AR tfibsegs B ly' S' W mem' md' ->
  spZ regs' = sp0 - 112 -> sp0 mod 16 = 0 -> alloc_ceiling <= sp0 - 8304 -> sp0 <= 2 ^ 47 ->
  (forall a, sp0 - 8304 <= a < sp0 -> apresent (w_H W) mem' a) ->
  as_got_shadow B = A_GOT_shadow -> as_shadow_cell B = A_shadow_glob ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (sp0 - 8) 8 ra0 ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (sp0 - 16) 8 v0 ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (sp0 - 24) 8 v1 ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (sp0 - 32) 8 v2 ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (sp0 - 40) 8 v3 ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (sp0 - 48) 8 v4 ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (sp0 - 56) 8 v5 ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (sp0 - 64) 8 v6 ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (sp0 - 72) 8 v7 ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (sp0 - 80) 8 v8 ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (sp0 - 88) 8 v9 ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (sp0 - 96) 8 v10 ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (sp0 - 104) 8 v11 ->
  0 <= ra0 < 2 ^ 64 -> 0 <= v0 < 2 ^ 64 -> 0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> 0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 -> 0 <= v5 < 2 ^ 64 -> 0 <= v6 < 2 ^ 64 -> 0 <= v7 < 2 ^ 64 -> 0 <= v8 < 2 ^ 64 ->
  0 <= v9 < 2 ^ 64 -> 0 <= v10 < 2 ^ 64 -> 0 <= v11 < 2 ^ 64 ->
  st_ok tfibsegs (Ereg regs' (map w64 [SBz; ra0; v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11])) (ss_hp_at pc)
    (restrict (w_H W) (mkst regs' (Z_to_bv 64 pc) mem' (seg_rom tfibsegs))).
Proof.
intros pc ly' S' W regs' mem' md' sp0 ra0 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  HAR Hsp Hal16 Hcl Hhi Hpres HGOT HCEL Mra M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11
  Rra R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11.
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR. unfold YG0f.ASAN_CEIL in CR.
set (EV := map w64 [SBz; ra0; v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11]).
assert (X2 : ew (Ereg regs' EV) 2 = getr regs' 2) by exact (ew_Ereg_nat regs' EV 2 2%bv eq_refl).
assert (X32 : ew (Ereg regs' EV) 32 = w64 SBz) by exact (ew_Ereg_extra regs' EV 0).
assert (Usp : bv_unsigned (ew (Ereg regs' EV) 2) = sp0 - 112) by (rewrite X2; exact Hsp).
assert (X45 : ew (Ereg regs' EV) 45 = w64 v11) by exact (ew_Ereg_extra regs' EV 13).
assert (X44 : ew (Ereg regs' EV) 44 = w64 v10) by exact (ew_Ereg_extra regs' EV 12).
assert (X43 : ew (Ereg regs' EV) 43 = w64 v9) by exact (ew_Ereg_extra regs' EV 11).
assert (X42 : ew (Ereg regs' EV) 42 = w64 v8) by exact (ew_Ereg_extra regs' EV 10).
assert (X41 : ew (Ereg regs' EV) 41 = w64 v7) by exact (ew_Ereg_extra regs' EV 9).
assert (X40 : ew (Ereg regs' EV) 40 = w64 v6) by exact (ew_Ereg_extra regs' EV 8).
assert (X39 : ew (Ereg regs' EV) 39 = w64 v5) by exact (ew_Ereg_extra regs' EV 7).
assert (X38 : ew (Ereg regs' EV) 38 = w64 v4) by exact (ew_Ereg_extra regs' EV 6).
assert (X37 : ew (Ereg regs' EV) 37 = w64 v3) by exact (ew_Ereg_extra regs' EV 5).
assert (X36 : ew (Ereg regs' EV) 36 = w64 v2) by exact (ew_Ereg_extra regs' EV 4).
assert (X35 : ew (Ereg regs' EV) 35 = w64 v1) by exact (ew_Ereg_extra regs' EV 3).
assert (X34 : ew (Ereg regs' EV) 34 = w64 v0) by exact (ew_Ereg_extra regs' EV 2).
assert (X33 : ew (Ereg regs' EV) 33 = w64 ra0) by exact (ew_Ereg_extra regs' EV 1).
destruct (al_const _ _ LAWS ly' S' W mem' md' HAR) as (Kcell & _ & Kgot & _).
rewrite HGOT, HCEL in Kgot. rewrite HCEL in Kcell.
rewrite restrict_mkst_fx. unfold ss_hp_at. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold hp_loop_regions. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  + unfold hp_frame_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable tfibsegs); apply Hpres; lia|].
    apply Forall_cons;
    [ apply (chunk_ok_val tfibsegs (Ereg regs' EV) _ (sp0 - 112) 8 8 (SOff 45 0) v11);
      [cbn [sv_denot]; rewrite X45; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | cbn; lia | cbn; lia | replace (sp0 - 112 + 8) with (sp0 - 104) by lia; exact M11] |].
    apply Forall_cons;
    [ apply (chunk_ok_val tfibsegs (Ereg regs' EV) _ (sp0 - 112) 16 8 (SOff 44 0) v10);
      [cbn [sv_denot]; rewrite X44; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | cbn; lia | cbn; lia | replace (sp0 - 112 + 16) with (sp0 - 96) by lia; exact M10] |].
    apply Forall_cons;
    [ apply (chunk_ok_val tfibsegs (Ereg regs' EV) _ (sp0 - 112) 24 8 (SOff 43 0) v9);
      [cbn [sv_denot]; rewrite X43; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | cbn; lia | cbn; lia | replace (sp0 - 112 + 24) with (sp0 - 88) by lia; exact M9] |].
    apply Forall_cons;
    [ apply (chunk_ok_val tfibsegs (Ereg regs' EV) _ (sp0 - 112) 32 8 (SOff 42 0) v8);
      [cbn [sv_denot]; rewrite X42; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | cbn; lia | cbn; lia | replace (sp0 - 112 + 32) with (sp0 - 80) by lia; exact M8] |].
    apply Forall_cons;
    [ apply (chunk_ok_val tfibsegs (Ereg regs' EV) _ (sp0 - 112) 40 8 (SOff 41 0) v7);
      [cbn [sv_denot]; rewrite X41; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | cbn; lia | cbn; lia | replace (sp0 - 112 + 40) with (sp0 - 72) by lia; exact M7] |].
    apply Forall_cons;
    [ apply (chunk_ok_val tfibsegs (Ereg regs' EV) _ (sp0 - 112) 48 8 (SOff 40 0) v6);
      [cbn [sv_denot]; rewrite X40; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | cbn; lia | cbn; lia | replace (sp0 - 112 + 48) with (sp0 - 64) by lia; exact M6] |].
    apply Forall_cons;
    [ apply (chunk_ok_val tfibsegs (Ereg regs' EV) _ (sp0 - 112) 56 8 (SOff 39 0) v5);
      [cbn [sv_denot]; rewrite X39; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | cbn; lia | cbn; lia | replace (sp0 - 112 + 56) with (sp0 - 56) by lia; exact M5] |].
    apply Forall_cons;
    [ apply (chunk_ok_val tfibsegs (Ereg regs' EV) _ (sp0 - 112) 64 8 (SOff 38 0) v4);
      [cbn [sv_denot]; rewrite X38; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | cbn; lia | cbn; lia | replace (sp0 - 112 + 64) with (sp0 - 48) by lia; exact M4] |].
    apply Forall_cons;
    [ apply (chunk_ok_val tfibsegs (Ereg regs' EV) _ (sp0 - 112) 72 8 (SOff 37 0) v3);
      [cbn [sv_denot]; rewrite X37; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | cbn; lia | cbn; lia | replace (sp0 - 112 + 72) with (sp0 - 40) by lia; exact M3] |].
    apply Forall_cons;
    [ apply (chunk_ok_val tfibsegs (Ereg regs' EV) _ (sp0 - 112) 80 8 (SOff 36 0) v2);
      [cbn [sv_denot]; rewrite X36; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | cbn; lia | cbn; lia | replace (sp0 - 112 + 80) with (sp0 - 32) by lia; exact M2] |].
    apply Forall_cons;
    [ apply (chunk_ok_val tfibsegs (Ereg regs' EV) _ (sp0 - 112) 88 8 (SOff 35 0) v1);
      [cbn [sv_denot]; rewrite X35; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | cbn; lia | cbn; lia | replace (sp0 - 112 + 88) with (sp0 - 24) by lia; exact M1] |].
    apply Forall_cons;
    [ apply (chunk_ok_val tfibsegs (Ereg regs' EV) _ (sp0 - 112) 96 8 (SOff 34 0) v0);
      [cbn [sv_denot]; rewrite X34; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | cbn; lia | cbn; lia | replace (sp0 - 112 + 96) with (sp0 - 16) by lia; exact M0] |].
    apply Forall_cons;
    [ apply (chunk_ok_val tfibsegs (Ereg regs' EV) _ (sp0 - 112) 104 8 (SOff 33 0) ra0);
      [cbn [sv_denot]; rewrite X33; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | cbn; lia | cbn; lia | replace (sp0 - 112 + 104) with (sp0 - 8) by lia; exact Mra] |].
    apply Forall_nil.
  + unfold hp_got_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold A_GOT_shadow; lia|]. split; [unfold A_GOT_shadow; lia|].
    split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val tfibsegs _ _ 0 A_GOT_shadow 8 (SLit A_shadow_glob) A_shadow_glob);
      [reflexivity | unfold A_shadow_glob; cbn; lia | cbn; lia |].
    cbn [Z.add]. exact (val_mem_of_rdword tfibsegs _ _ _ _ Kgot).
  + unfold hp_cell_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold A_shadow_glob; lia|]. split; [unfold A_shadow_glob; lia|].
    split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val tfibsegs _ _ 0 A_shadow_glob 8 (SOff 32 0) SBz);
      [cbn [sv_denot]; rewrite X32; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SBz; cbn; lia | cbn; lia |].
    cbn [Z.add]. unfold SBz. exact (val_mem_of_rdword tfibsegs _ _ _ _ Kcell).
- apply pairwise_disjoint_of_extents. unfold hp_loop_regions, hp_frame_region, hp_got_region, hp_cell_region,
    extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold A_GOT_shadow, A_shadow_glob. repeat split; lia.
- split; [|split; exact I]. cbn [hp_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite X2, X32. change (2 ^ 4) with 16. unfold w64, SBz. rewrite unsigned_lit_small by lia.
  rewrite Z.pow_0_r, Z.mod_1_r. unfold spZ in Hsp. rewrite Hsp.
  repeat split; try lia.
Qed.
Lemma hp_epi : forall (Q : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  ly S W0 W regs mem md ly' S' (regs' : bvmap 5 word) mem' md' res,
  ajournal tfibsegs B STK_has_prefixed (spZ regs) [] ly S W0 mem md [] ly' S' W mem' md' 0 ->
  YK0s.ret_ok (getr regs 1) -> getr regs' 3 = w64 (as_gp B) -> getr regs' 4 = w64 (as_tp B) ->
  as_got_shadow B = A_GOT_shadow -> as_shadow_cell B = A_shadow_glob ->
  spZ regs' = spZ regs - 112 -> getr regs' 10 = w64 res -> 0 <= res < 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (spZ regs - 48) 8 (bv_unsigned (getr regs 20)) ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (spZ regs - 56) 8 (bv_unsigned (getr regs 21)) ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (spZ regs - 64) 8 (bv_unsigned (getr regs 22)) ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (spZ regs - 72) 8 (bv_unsigned (getr regs 23)) ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (spZ regs - 80) 8 (bv_unsigned (getr regs 24)) ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (spZ regs - 88) 8 (bv_unsigned (getr regs 25)) ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (spZ regs - 96) 8 (bv_unsigned (getr regs 26)) ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (spZ regs - 104) 8 (bv_unsigned (getr regs 27)) ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  (forall regs2 mem2 md2, getr regs2 10 = w64 res -> aregs_preserved regs regs2 ->
     ajournal tfibsegs B STK_has_prefixed (spZ regs) [] ly S W0 mem md [] ly' S' W mem2 md2 0 ->
     gframe tfibsegs W (spZ regs - 8304) (spZ regs) mem' mem2 ->
     Q ly' S' W regs2 mem2 md2) ->
  SRr tfibsegs W (cfg_at tfibsegs A_hp_epi regs' mem' md')
    (apost_base tfibsegs B STK_has_prefixed [] regs ly S W0 mem md 0 Q).
Proof.
intros Q ly S W0 W regs mem md ly' S' regs' mem' md' res HJ Hra Hgp Htp HGOT HCEL Hsp Ha0 Hres
  Mra M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 HGP HTP HQ.
pose proof g2_segs_low as Hsegs. pose proof g2_wx as Hwx.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR. unfold YG0f.ASAN_CEIL in CR.
assert (FFS : STK_has_prefixed = 8304) by reflexivity.
pose proof (hp_loop_entry A_hp_epi ly' S' W regs' mem' md' (spZ regs)
  (bv_unsigned (getr regs 1)) (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9))
  (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 20))
  (bv_unsigned (getr regs 21)) (bv_unsigned (getr regs 22)) (bv_unsigned (getr regs 23))
  (bv_unsigned (getr regs 24)) (bv_unsigned (getr regs 25)) (bv_unsigned (getr regs 26))
  (bv_unsigned (getr regs 27)) HAR Hsp Hal16 ltac:(rewrite FFS in *; lia) ltac:(lia)
  ltac:(intros a Ha; apply Hpres; rewrite FFS; lia) HGOT HCEL
  Mra M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11
  (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
  (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)) as HS.
set (EV := map w64 [SBz; bv_unsigned (getr regs 1); bv_unsigned (getr regs 8); bv_unsigned (getr regs 9);
  bv_unsigned (getr regs 18); bv_unsigned (getr regs 19); bv_unsigned (getr regs 20); bv_unsigned (getr regs 21);
  bv_unsigned (getr regs 22); bv_unsigned (getr regs 23); bv_unsigned (getr regs 24); bv_unsigned (getr regs 25);
  bv_unsigned (getr regs 26); bv_unsigned (getr regs 27)]) in HS.
assert (X2 : bv_unsigned (ew (Ereg regs' EV) 2) = spZ regs - 112)
  by (rewrite (ew_Ereg_nat regs' EV 2 2%bv eq_refl); exact Hsp).
assert (SHOK : sh_ok tfibsegs hp_Bx [] (Ereg regs' EV) (mrestrict (w_H W) mem')) by apply Forall_nil.
unfold cfg_at. change (w64 A_hp_epi) with (Z_to_bv 64 A_hp_epi).
aj_run_tok tbl_hp_ok HS HJ SHOK hp_Bspan.
{ eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ _ _ 2%nat (-112));
    [reflexivity | rewrite X2; lia | cbn; lia | cbn; lia | awr_ok_tac]. }
pose proof (gframe_of_frame tfibsegs W (Ereg regs' EV) _ 2 8 112 (spZ regs - 112)
  (spZ regs - 8304) (spZ regs) mem' (ms_mem ms) HFr ltac:(vm_compute; reflexivity) X2
  ltac:(lia) ltac:(lia)) as GE.
clear HF HFr HG.
assert (X33 : ew (Ereg regs' EV) 33 = w64 (bv_unsigned (getr regs 1))) by exact (ew_Ereg_extra regs' EV 1).
assert (X34 : ew (Ereg regs' EV) 34 = w64 (bv_unsigned (getr regs 8))) by exact (ew_Ereg_extra regs' EV 2).
assert (X35 : ew (Ereg regs' EV) 35 = w64 (bv_unsigned (getr regs 9))) by exact (ew_Ereg_extra regs' EV 3).
assert (X36 : ew (Ereg regs' EV) 36 = w64 (bv_unsigned (getr regs 18))) by exact (ew_Ereg_extra regs' EV 4).
assert (X37 : ew (Ereg regs' EV) 37 = w64 (bv_unsigned (getr regs 19))) by exact (ew_Ereg_extra regs' EV 5).
assert (X38 : ew (Ereg regs' EV) 38 = w64 (bv_unsigned (getr regs 20))) by exact (ew_Ereg_extra regs' EV 6).
assert (X39 : ew (Ereg regs' EV) 39 = w64 (bv_unsigned (getr regs 21))) by exact (ew_Ereg_extra regs' EV 7).
assert (X40 : ew (Ereg regs' EV) 40 = w64 (bv_unsigned (getr regs 22))) by exact (ew_Ereg_extra regs' EV 8).
assert (X41 : ew (Ereg regs' EV) 41 = w64 (bv_unsigned (getr regs 23))) by exact (ew_Ereg_extra regs' EV 9).
assert (X42 : ew (Ereg regs' EV) 42 = w64 (bv_unsigned (getr regs 24))) by exact (ew_Ereg_extra regs' EV 10).
assert (X43 : ew (Ereg regs' EV) 43 = w64 (bv_unsigned (getr regs 25))) by exact (ew_Ereg_extra regs' EV 11).
assert (X44 : ew (Ereg regs' EV) 44 = w64 (bv_unsigned (getr regs 26))) by exact (ew_Ereg_extra regs' EV 12).
assert (X45 : ew (Ereg regs' EV) 45 = w64 (bv_unsigned (getr regs 27))) by exact (ew_Ereg_extra regs' EV 13).
rreg HS (1%bv : bv 5) P1.
rreg HS (2%bv : bv 5) P2.
rreg HS (3%bv : bv 5) P3.
rreg HS (4%bv : bv 5) P4.
rreg HS (8%bv : bv 5) P8.
rreg HS (9%bv : bv 5) P9.
rreg HS (10%bv : bv 5) P10.
rreg HS (18%bv : bv 5) P18.
rreg HS (19%bv : bv 5) P19.
rreg HS (20%bv : bv 5) P20.
rreg HS (21%bv : bv 5) P21.
rreg HS (22%bv : bv 5) P22.
rreg HS (23%bv : bv 5) P23.
rreg HS (24%bv : bv 5) P24.
rreg HS (25%bv : bv 5) P25.
rreg HS (26%bv : bv 5) P26.
rreg HS (27%bv : bv 5) P27.
eapply (SRr_ret_at tfibsegs tbl_hp tbl_hp_ok Hwx W (Ereg regs' EV) _ _ _ _ HS eq_refl
  ltac:(vm_compute; reflexivity)).
intros matR.
lazymatch goal with |- apost_base _ _ _ _ _ _ _ _ _ _ _ _ _ (mkCfg (mkst ?r _ ?m _) ?d) =>
  exists ly', S', r, m, d end.
split.
{ cbn [ms_regs]. rewrite P1, X33. unfold w64. rewrite Z_to_bv_bv_unsigned, Hra. reflexivity. }
pose proof (ajournal_materialize tfibsegs B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ matR HJ) as HJm.
split; [cbn [ms_mem]; exact HJm|].
assert (HPR : aregs_preserved regs (ms_regs ms)).
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hcase : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22
                  \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27 \/ False) by lia.
  repeat (destruct Hcase as [-> | Hcase]);
  [ replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity); rewrite P2, (ew_Ereg_nat regs' EV 2 2%bv eq_refl);
    unfold spZ in Hsp; rewrite Hsp;
    replace (bv_unsigned (getr regs 2) - 112 + 112) with (bv_unsigned (getr regs 2)) by lia;
    apply Z_to_bv_bv_unsigned
  | replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity); rewrite P3, (ew_Ereg_nat regs' EV 3 3%bv eq_refl), Hgp, HGP; reflexivity
  | replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity); rewrite P4, (ew_Ereg_nat regs' EV 4 4%bv eq_refl), Htp, HTP; reflexivity
  | replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity); rewrite P8, X34; unfold w64;
    apply Z_to_bv_bv_unsigned
  | replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity); rewrite P9, X35; unfold w64;
    apply Z_to_bv_bv_unsigned
  | replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity); rewrite P18, X36; unfold w64;
    apply Z_to_bv_bv_unsigned
  | replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity); rewrite P19, X37; unfold w64;
    apply Z_to_bv_bv_unsigned
  | replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity); rewrite P20, X38; unfold w64;
    apply Z_to_bv_bv_unsigned
  | replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity); rewrite P21, X39; unfold w64;
    apply Z_to_bv_bv_unsigned
  | replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity); rewrite P22, X40; unfold w64;
    apply Z_to_bv_bv_unsigned
  | replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity); rewrite P23, X41; unfold w64;
    apply Z_to_bv_bv_unsigned
  | replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity); rewrite P24, X42; unfold w64;
    apply Z_to_bv_bv_unsigned
  | replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity); rewrite P25, X43; unfold w64;
    apply Z_to_bv_bv_unsigned
  | replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity); rewrite P26, X44; unfold w64;
    apply Z_to_bv_bv_unsigned
  | replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity); rewrite P27, X45; unfold w64;
    apply Z_to_bv_bv_unsigned
  | destruct Hcase ]. }
split; [exact HPR|].
apply HQ; [cbn [ms_regs]; rewrite P10, (ew_Ereg_nat regs' EV 10 10%bv eq_refl); exact Ha0
          | exact HPR | exact HJm | exact GE].
Qed.

(* the epilogue from a loop state whose a0 holds the answer *)
Lemma hp_ret : forall cx a lyc Sc W regs m mdc, hp_st cx a lyc Sc W regs m mdc -> getr regs 10 = w64 (hp_res cx) ->
  SRr tfibsegs W (cfg_at tfibsegs A_hp_epi regs m mdc) (hp_post cx).
Proof.
intros cx a lyc Sc W regs m mdc H H10.
pose proof (hp_st_static cx a lyc Sc W regs m mdc H) as (Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof H as (HE & HJ & Hab & Q3 & Q4 & Hsp & HF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgl).
pose proof HE as (Hra & G3 & G4 & _).
pose proof HF as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13).
assert (Hres : 0 <= hp_res cx < 2 ^ 64) by (unfold hp_res; destruct (ManifestModel.token _ _ _); lia).
assert (FFS : STK_has_prefixed = 8304) by reflexivity.
unfold hp_post.
apply (hp_epi (hp_Q cx) (cx_ly cx) (cx_S cx) (cx_W0 cx) W (cx_regs0 cx) (cx_mem cx) (cx_md cx) lyc Sc regs m mdc
  (hp_res cx) HJ Hra Q3 Q4 (tl_got_shadow B TL) (tl_shadow_cell B TL) Hsp H10 Hres
  V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 V13 G3 G4).
intros regs2 mem2 md2 Ha0 _ _ GF.
split; [exact Ha0|]. split; [exact Hab|].
apply (fm_glob_gframe tfibsegs W _ _ m mem2 _ _ _ _ GF); [rewrite FFS in *; lia | exact Hgl].
Qed.
(* the epilogue one step after a loop state, for a path that overwrites s5 first (the tail's NULL answer:
   `mv s5,a0` then `j 0x82280`): the step keeps sp/gp/tp and writes nothing outside [sp0 - 8304, sp0 - 104) *)
Lemma hp_ret_step : forall cx a lyc Sc W regs m mdc regs' m' mdc',
  hp_st cx a lyc Sc W regs m mdc ->
  ajournal tfibsegs B STK_has_prefixed (spZ (cx_regs0 cx)) [] (cx_ly cx) (cx_S cx) (cx_W0 cx) (cx_mem cx) (cx_md cx)
    [] lyc Sc W m' mdc' 0 ->
  gframe tfibsegs W (spZ (cx_regs0 cx) - STK_has_prefixed) (spZ (cx_regs0 cx) - 104) m m' ->
  regs_keep [2; 3; 4]%bv regs regs' ->
  getr regs' 10 = w64 (hp_res cx) ->
  SRr tfibsegs W (cfg_at tfibsegs A_hp_epi regs' m' mdc') (hp_post cx).
Proof.
intros cx a lyc Sc W regs m mdc regs' m' mdc' H HJ' HG HK H10.
pose proof (hp_st_static cx a lyc Sc W regs m mdc H) as (Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof H as (HE & _ & Hab & Q3 & Q4 & Hsp & HF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgl).
pose proof HE as (Hra & G3 & G4 & _).
assert (FFS : STK_has_prefixed = 8304) by reflexivity.
ceil2.
pose proof (hp_frame_gframe W (cx_regs0 cx) m m' _ _ HG ltac:(lia) ltac:(rewrite FFS in *; lia) ltac:(lia) HF) as HF'.
pose proof HF' as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13).
assert (Hres : 0 <= hp_res cx < 2 ^ 64) by (unfold hp_res; destruct (ManifestModel.token _ _ _); lia).
assert (K : forall r, In r [2; 3; 4]%bv -> getr regs' r = getr regs r) by exact HK.
assert (Q3' : getr regs' 3 = w64 (as_gp B)) by (rewrite K by (cbv; tauto); exact Q3).
assert (Q4' : getr regs' 4 = w64 (as_tp B)) by (rewrite K by (cbv; tauto); exact Q4).
assert (Hsp' : spZ regs' = spZ (cx_regs0 cx) - 112) by (unfold spZ; rewrite K by (cbv; tauto); exact Hsp).
unfold hp_post.
apply (hp_epi (hp_Q cx) (cx_ly cx) (cx_S cx) (cx_W0 cx) W (cx_regs0 cx) (cx_mem cx) (cx_md cx) lyc Sc regs' m' mdc'
  (hp_res cx) HJ' Hra Q3' Q4' (tl_got_shadow B TL) (tl_shadow_cell B TL) Hsp' H10 Hres
  V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 V13 G3 G4).
intros regs2 mem2 md2 Ha0 _ _ GF.
split; [exact Ha0|]. split; [exact Hab|].
apply (fm_glob_gframe tfibsegs W _ _ m mem2 _ _ _ _ (gframe_seq tfibsegs W _ _ m m' mem2
  (gframe_widen tfibsegs W (spZ (cx_regs0 cx) - 8304) (spZ (cx_regs0 cx)) _ _ m m' HG ltac:(rewrite FFS; lia)
    ltac:(lia)) GF)); [rewrite FFS in *; lia | exact Hgl].
Qed.

End a.
