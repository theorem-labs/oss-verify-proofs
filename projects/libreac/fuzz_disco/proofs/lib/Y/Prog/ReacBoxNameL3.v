(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC88.v:61-65, 107-112, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_L3.v, with its module paths and numbers changed; 1009 of its 1085 lines of code are new or changed and 1284 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC8i YC1f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YA0o YCbm YA0q YG0s YC1g YC1h YC4b YC44 YC81 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import SbCh ReacBoxNameLoops.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Definition rbn_lc (c : Z) : Z := if (65 <=? c) && (c <=? 90) then c + 32 else c.
Lemma rbn_lc_range : forall c, 0 <= c < 256 -> 0 <= rbn_lc c < 256.
Proof.
intros c Hc. unfold rbn_lc.
destruct (Z.leb_spec 65 c); destruct (Z.leb_spec c 90); cbn [andb]; lia.
Qed.
Lemma bn_tk_cons : forall sn c l,
  bn_tk sn (c :: l) = if (c =? 45) && negb sn then bn_tk true l else rbn_lc c :: bn_tk sn l.
Proof.
intros sn c l. cbn [bn_tk]. unfold rbn_lc.
destruct ((c =? 45) && negb sn); reflexivity.
Qed.
Lemma bn_tk_len : forall l sn, (length (bn_tk sn l) <= length l)%nat.
Proof.
induction l as [|c r IH]; intros sn; [cbn; lia|].
rewrite bn_tk_cons. pose proof (IH true). pose proof (IH sn).
destruct ((c =? 45) && negb sn); cbn [length]; lia.
Qed.
Definition RBN_L3J : Z := 0x4a0.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Definition rbn3_B : sv := SOff 22 0.
Definition rbn3_span : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition rbn3h_ss : sstate :=
  mkSS (AF_both3_reac_box_name + RBN_L3) (sr_set (sr_set sr_atoms 20%bv (SLit 24)) 24%bv (SLit 45))
    [ YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))] ] None
    (mkFacts [ (22%nat, mkAF SB SB 0); (21%nat, mkAF 0 22 0); (26%nat, mkAF 0 1 0);
               (32%nat, mkAF 0 (2 ^ 47 - 1) 0); (33%nat, mkAF 0 255 0) ] []
      [(SAlu ALU_ADD (SOff 27 0) (SOff 21 0), SOff 32 0)]).
Definition rbn3_E (regs : bvmap 5 word) (q c : Z) : env := Eimg (Ereg regs (map (Z_to_bv 64) [q; c])).
Lemma rbn3_ew : forall regs q c,
  ew (rbn3_E regs q c) 32 = Z_to_bv 64 q /\ ew (rbn3_E regs q c) 33 = Z_to_bv 64 c /\
  (forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (rbn3_E regs q c) k = getr regs r).
Proof.
intros regs q c. unfold rbn3_E.
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)|].
intros k r Hk. apply ew_Eimg_Ereg_nat. exact Hk.
Qed.
Lemma rbn3h_entry : forall (fq : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) memc N i c (sn : bool),
  getr regs 20 = w64 24 -> getr regs 24 = w64 45 -> getr regs 22 = w64 SHADOW_OFF ->
  getr regs 21 = w64 i -> getr regs 26 = w64 (if sn then 1 else 0) -> getr regs 27 = w64 N ->
  0 <= i <= 22 -> 0 <= N -> N + i <= 2 ^ 47 - 1 ->
  val_mem SEGS (mrestrict (w_H W) memc) (N + i) 1 c -> 0 <= c < 256 ->
  st_ok_pi SEGS VAL (rbn3_E regs (N + i) c) rbn3h_ss
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L3))) memc (seg_rom SEGS))).
Proof.
intros fq W regs memc N i c sn H20 H24 H22 H21 H26 H27 Hi HN HNi Vc Rc.
rewrite restrict_mkst_fx.
destruct (rbn3_ew regs (N + i) c) as (E32 & E33 & EE).
assert (HR : regs_ok (rbn3_E regs (N + i) c) (sr_set (sr_set sr_atoms 20%bv (SLit 24)) 24%bv (SLit 45)) regs).
{ apply regs_ok_pin; [|discriminate | cbn [sv_denot]; exact H24].
  apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | discriminate | cbn [sv_denot]; exact H20]. }
remember (rbn3_E regs (N + i) c) as E eqn:HE. clear HE.
assert (E22 : ew E 22 = Z_to_bv 64 SB) by (rewrite (EE 22%nat 22%bv eq_refl); exact H22).
assert (E21 : ew E 21 = Z_to_bv 64 i) by (rewrite (EE 21%nat 21%bv eq_refl); exact H21).
assert (E26 : ew E 26 = Z_to_bv 64 (if sn then 1 else 0)) by (rewrite (EE 26%nat 26%bv eq_refl); exact H26).
assert (E27 : ew E 27 = Z_to_bv 64 N) by (rewrite (EE 27%nat 27%bv eq_refl); exact H27).
assert (Hsn : 0 <= (if sn then 1 else 0) <= 1) by (destruct sn; lia).
unfold rbn3h_ss. apply pa_entry_st_ok_full.
- exact HR.
- vm_compute. reflexivity.
- constructor; [|constructor]; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  cbn [base_val]. rewrite E32, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (N + i) 0 1 (SOff 33 0) c);
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |].
  rewrite Z.add_0_r. exact Vc.
- apply pairwise_disjoint_of_extents.
  unfold extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  cbn [zpairwise_disjoint zall_disjoint]. tauto.
- split; [|split; [exact I|]].
  + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E22, E21, E26, E32, E33, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold SB. repeat split; lia.
  + cbn [f_alias alias_ok]. split; [|exact I].
    apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom E 27 N E27), (U_atom E 21 i E21), (U_atom E 32 (N + i) E32) by lia.
    apply zcanon_id. unfold M64. lia.
Qed.
Definition rbn3_lowf (c : Z) : Z :=
  zcanon (Z.land (zcanon (zcanon (c + 0) + zcanon (Z.shiftl
    (zcanon (if zcanon (Z.land (zcanon (c + -65)) (zcanon 255)) <? zcanon 26 then 1 else 0))
    (Z.land (zcanon 5) 63)))) (zcanon 255)).
Lemma rbn3_lowf_ok : forall c, 0 <= c < 256 -> rbn3_lowf c = rbn_lc c.
Proof.
assert (A : forallb (fun x => rbn3_lowf x =? rbn_lc x) (map Z.of_nat (seq 0 256)) = true)
  by (vm_compute; reflexivity).
intros c Hc. rewrite forallb_forall in A. apply Z.eqb_eq. apply A.
apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.
Lemma rbn3_lower : forall E n c, ew E n = Z_to_bv 64 c -> 0 <= c < 256 ->
  U E (SAlu ALU_AND (SAlu ALU_ADD (SOff n 0)
    (SAlu ALU_SLL (SAlu ALU_SLTU (SAlu ALU_AND (SOff n (-65)) (SLit 255)) (SLit 26)) (SLit 5))) (SLit 255))
  = rbn_lc c.
Proof.
intros E n c Hn Hc. rewrite <- (rbn3_lowf_ok c Hc). unfold rbn3_lowf.
rewrite !U_SAlu, !U_SLit, !U_SOff, Hn, unsigned_lit_small by lia. cbn [zalu_raw]. reflexivity.
Qed.
Lemma rbn3_keep_of_bv : forall (regs regs2 : bvmap 5 word) (cl : list Z) (l : list (bv 5)),
  (forall rr : bv 5, In rr l -> getr regs2 rr = getr regs rr) ->
  (forall r : Z, 0 <= r < 32 -> ~ In r cl -> r = 0 \/ In (Z_to_bv 5 r) l) ->
  rbn_keep_regs regs regs2 cl.
Proof.
intros regs regs2 cl l HK Hc r Hr Hn. destruct (Hc r Hr Hn) as [-> | Hin]; [reflexivity|].
apply HK. exact Hin.
Qed.
Ltac rbn3_cover_tac :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hn := fresh "Hn" in let H32 := fresh "H32" in
  intros r Hr Hn;
  assert (H32 : r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7 \/ r = 8 \/ r = 9 \/
    r = 10 \/ r = 11 \/ r = 12 \/ r = 13 \/ r = 14 \/ r = 15 \/ r = 16 \/ r = 17 \/ r = 18 \/ r = 19 \/
    r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27 \/ r = 28 \/ r = 29 \/
    r = 30 \/ r = 31) by lia;
  repeat (destruct H32 as [-> | H32]); try (subst r);
  first [ solve [left; reflexivity]
        | solve [exfalso; apply Hn; cbn [In]; repeat first [ solve [left; reflexivity] | right ]]
        | solve [right; cbn [app In]; repeat first [ solve [left; apply bv_eq; vm_compute; reflexivity] | right ]] ].
Definition rbn3h_cl : list Z := [1; 10; 11; 12; 26].
Definition rbn3h_kl : list (bv 5) :=
  [2; 3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 18; 19; 21; 22; 23; 25; 27; 28; 29; 30; 31]%bv.
Lemma rbn3_keep_pin : forall (regs regs2 : bvmap 5 word),
  getr regs 20 = w64 24 -> getr regs 24 = w64 45 ->
  getr regs2 20 = Z_to_bv 64 24 -> getr regs2 24 = Z_to_bv 64 45 ->
  (forall rr : bv 5, In rr rbn3h_kl -> getr regs2 rr = getr regs rr) ->
  rbn_keep_regs regs regs2 rbn3h_cl.
Proof.
intros regs regs2 A20 A24 B20 B24 HK.
apply (rbn3_keep_of_bv regs regs2 rbn3h_cl (rbn3h_kl ++ [20; 24]%bv)).
- intros rr Hin. apply in_app_or in Hin. destruct Hin as [Hin | [<- | [<- | []]]].
  + apply HK. exact Hin.
  + rewrite A20, B20. reflexivity.
  + rewrite A24, B24. reflexivity.
- unfold rbn3h_cl, rbn3h_kl. rbn3_cover_tac.
Qed.
Definition rbn3j_cl : list Z := [10; 21].
Definition rbn3j_kl : list (bv 5) :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma rbn3j_cover : forall r : Z, 0 <= r < 32 -> ~ In r rbn3j_cl -> r = 0 \/ In (Z_to_bv 5 r) rbn3j_kl.
Proof. unfold rbn3j_cl, rbn3j_kl. rbn3_cover_tac. Qed.
Ltac rbn3_nowin :=
  let bq := fresh "bq" in let wl := fresh "wl" in let wh := fresh "wh" in let aq := fresh "aq" in
  let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros bq wl wh aq Hin Ha;
  lazymatch type of Hin with In _ (windows ?rs) =>
    let v := eval vm_compute in (windows rs) in change (In (bq, wl, wh) v) in Hin end;
  cbn [In] in Hin;
  repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; lia |]);
  try destruct Hin.
Ltac rbn3_upd KEEP GROW :=
  lazymatch goal with
  | HFr : frame_of ?Ef ?rs (mrestrict (w_H ?Wx) ?m0) (mrestrict (w_H ?Wx) ?m1),
    HG : mem_grows (mrestrict (w_H ?Wx) ?m0) (mrestrict (w_H ?Wx) ?m1) |- _ =>
    lazymatch type of KEEP with forall a, _ -> aview ?sg _ m0 a = aview _ _ ?mo a =>
    let K2 := fresh "K2" in let G2 := fresh "G2" in
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> aview sg (w_H Wx) m1 a = aview sg (w_H Wx) mo a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; refine (eq_trans _ (KEEP a Ha));
          apply (kept_of_frame Ef rs (w_H Wx) m0 m1 (fun _ => False) HFr); [rbn3_nowin | exact Ha | intros []]);
    assert (G2 : mem_grows (mrestrict (w_H Wx) mo) (mrestrict (w_H Wx) m1))
      by (eapply mem_grows_trans; [exact GROW | exact HG]);
    clear KEEP GROW HFr HG; try (match goal with HF : frame_of _ _ _ _ |- _ => clear HF end);
    rename K2 into KEEP; rename G2 into GROW
    end end.
Ltac rbn3_awr :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
Ltac rbn3_U H n v := rewrite (U_atom _ n v) in H by first [lia | rewrite ?ew_ewset_other by lia; assumption].
Ltac rbn3_rreg HS r Hr :=
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
Lemma rbn3_aview_wrap : forall H (m : word -> option byte) a, aview SEGS H m a = aview SEGS H m (a mod 2 ^ 64).
Proof.
intros H m a. unfold aview, mbyte, mrestrict.
replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Definition rbn3h_post (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS)
  (memc : word -> option byte) k (regs : bvmap 5 word) (c : Z) (sn : bool) : world SEGS -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md',
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k /\
    (forall a, aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) /\
    mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) mem') /\
    rbn_keep_regs regs regs' rbn3h_cl /\
    if (c =? 45) && negb sn then
      c' = cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + RBN_L3J) regs' mem' md' /\
      getr regs' 26 = w64 1
    else
      c' = cfg_at (fx := fq) SEGS (BASE + AF_both3_sb_ch) regs' mem' md' /\
      getr regs' 1 = w64 (BASE + AF_both3_reac_box_name + RBN_L3J) /\
      getr regs' 10 = w64 (spZ regs + 120) /\ getr regs' 11 = w64 (rbn_lc c) /\
      getr regs' 26 = getr regs 26.
Ltac rbn3_keep_all KEEP :=
  let a := fresh "a" in intros a; rewrite (rbn3_aview_wrap _ _ a); rewrite (rbn3_aview_wrap _ _ a);
  apply KEEP; apply Z.mod_pos_bound; lia.
Ltac rbn3_call_leaf HJ KEEP GROW HAE H20 H24 :=
  lazymatch goal with HS : st_ok _ ?Ex (setpc ?ssc (pa_sigma AS_sb_ch)) (restrict _ ?msc) |- _ =>
  let R1 := fresh "R1" in let R10 := fresh "R10" in let R11 := fresh "R11" in let R26 := fresh "R26" in
  let R20 := fresh "R20" in let R24 := fresh "R24" in let HK := fresh "HK" in
  prreg HS (1%bv : bv 5) R1; rbn3_rreg HS (10%bv : bv 5) R10; rbn3_rreg HS (11%bv : bv 5) R11;
  prreg HS (20%bv : bv 5) R20; prreg HS (24%bv : bv 5) R24;
  pose proof (regs_kept_of_st_ok SEGS Ex _ _ _ _ rbn3h_kl HS ltac:(env_agree_chain HAE)
    ltac:(vm_compute; reflexivity)) as HK;
  pose proof (regs_kept_of_st_ok SEGS Ex _ _ _ _ [26%bv] HS ltac:(env_agree_chain HAE)
    ltac:(vm_compute; reflexivity)) as R26;
  cbn [ms_regs restrict] in HK, R26;
  pmkst HS; rewrite pa_sigma_sb_ch;
  apply SRr_ret; unfold rbn3h_post; split; [reflexivity|];
  exists (ms_regs msc), (ms_mem msc);
  lazymatch goal with |- context [mkCfg _ ?mdx] => exists mdx end;
  split; [first [exact HJ | apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ]|];
  split; [rbn3_keep_all KEEP|]; split; [exact GROW|];
  split; [exact (rbn3_keep_pin _ (ms_regs msc) H20 H24 R20 R24 HK)|]
  end.
Lemma rbn3_head : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
  (regs : bvmap 5 word) N i c (sn : bool),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 20 = w64 24 -> getr regs 24 = w64 45 -> getr regs 22 = w64 SHADOW_OFF ->
  getr regs 21 = w64 i -> getr regs 26 = w64 (if sn then 1 else 0) -> getr regs 27 = w64 N ->
  getr regs 9 = getr regs 2 -> spZ regs + 120 < 2 ^ 64 ->
  0 <= i <= 22 -> 0 <= N -> N + i <= 2 ^ 47 - 1 ->
  val_mem SEGS (mrestrict (w_H W) memc) (N + i) 1 c -> 0 <= c < 256 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (N + i) 1 ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + RBN_L3) regs memc mdc)
    (rbn3h_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs c sn).
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs N i c sn HJ
  H20 H24 H22 H21 H26 H27 H9 Hsp Hi HN HNi Vc Rc HRA.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. unfold YImgTop.IMG_LO in HBLO.
pose proof (@paj_run fq _ _ _ _ _ B LAWS) as RUN.
pose proof (@paj_run_to fq _ _ _ _ _ B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
pose proof (rbn3h_entry fq W regs memc N i c sn H20 H24 H22 H21 H26 H27 Hi HN HNi Vc Rc) as HS.
destruct (rbn3_ew regs (N + i) c) as (E32 & E33 & EE).
set (E := rbn3_E regs (N + i) c) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, rbn3_E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (map (Z_to_bv 64) [N + i; c])) E)
  by (unfold E, rbn3_E; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E22 : ew E 22 = Z_to_bv 64 SB) by (rewrite (EE 22%nat 22%bv eq_refl); exact H22).
assert (E26 : ew E 26 = Z_to_bv 64 (if sn then 1 else 0)) by (rewrite (EE 26%nat 26%bv eq_refl); exact H26).
assert (E9 : ew E 9 = Z_to_bv 64 (spZ regs)) by (rewrite (EE 9%nat 9%bv eq_refl), H9; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (Hsp0 : 0 <= spZ regs) by (unfold spZ; pose proof (bv_unsigned_in_range 64 (getr regs 2)); lia).
assert (SHOK : sh_ok SEGS rbn3_B [] E (mrestrict (w_H W) memc)) by constructor.
assert (HUB : U E rbn3_B = SHADOW_OFF)
  by (unfold rbn3_B; rewrite (U_atom E 22 SB E22) by (unfold SB; lia); reflexivity).
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) memc a)
  by (intros; reflexivity).
assert (GROW : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) memc)) by apply mem_grows_refl.
unfold cfg_at. rewrite <- Z.add_assoc.
paj_run_tok RUN HS HJ SHOK rbn3_span.
{ cbn [ms_mem]. rewrite (U_atom E 32 (N + i) E32) by lia.
  apply (obl_of_range SEGS (w_H W) memc E rbn3_B (N + i) 1 (N + i) 1); [exact HRA | exact HUB | lia | lia]. }
{ rbn3_awr. }
rbn3_upd KEEP GROW.
psrr_branch_tok RUN BR HS SHOK rbn3_span.
- rewrite branch_ne_U in Hc. rbn3_U Hc 33%nat c. rewrite U_SLit in Hc. change (zcanon 45) with 45 in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  paj_run_tok RUN HS HJ SHOK rbn3_span.
  { rbn3_awr. }
  rbn3_upd KEEP GROW.
  rbn3_call_leaf HJ KEEP GROW HAE H20 H24.
  replace ((c =? 45) && negb sn) with false by (symmetry; apply andb_false_iff; left; apply Z.eqb_neq; exact Hc).
  cbv iota.
  split; [unfold cfg_at, w64; reflexivity|].
  split; [rewrite R1; unfold w64; f_equal; unfold AF_both3_reac_box_name, RBN_L3J; lia|].
  split; [rewrite R10; cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite E9; unfold w64;
          rewrite unsigned_lit_small by lia; reflexivity|].
  split; [rewrite R11, denot_lit_U, (rbn3_lower _ 33 c) by first [lia | rewrite ?ew_ewset_other by lia; assumption];
          reflexivity|].
  exact (R26 26%bv ltac:(cbv; tauto)).
- rewrite branch_ne_U in Hc. rbn3_U Hc 33%nat c. rewrite U_SLit in Hc. change (zcanon 45) with 45 in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc. subst c.
  paj_run_tok RUN HS HJ SHOK rbn3_span.
  { rbn3_awr. }
  rbn3_upd KEEP GROW.
  destruct sn.
  + psrr_branch_tok RUN BR HS SHOK rbn3_span.
    * paj_run_tok RUN HS HJ SHOK rbn3_span.
      { rbn3_awr. }
      rbn3_upd KEEP GROW.
      rbn3_call_leaf HJ KEEP GROW HAE H20 H24.
      change ((45 =? 45) && negb true) with false. cbv iota.
      split; [unfold cfg_at, w64; reflexivity|].
      split; [rewrite R1; unfold w64; f_equal; unfold AF_both3_reac_box_name, RBN_L3J; lia|].
      split; [rewrite R10; cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite E9; unfold w64;
              rewrite unsigned_lit_small by lia; reflexivity|].
      split; [rewrite R11, denot_lit_U, (rbn3_lower _ 33 45) by first [lia | rewrite ?ew_ewset_other by lia; assumption];
              reflexivity|].
      exact (R26 26%bv ltac:(cbv; tauto)).
    * exfalso. rewrite branch_ne_U in Hc. rbn3_U Hc 26%nat 1. rewrite U_SLit in Hc.
      vm_compute in Hc. discriminate Hc.
  + psrr_branch_tok RUN BR HS SHOK rbn3_span.
    * exfalso. rewrite branch_ne_U in Hc. rbn3_U Hc 26%nat 0. rewrite U_SLit in Hc.
      vm_compute in Hc. discriminate Hc.
    * paj_run_to_tok RUNTO HS HJ SHOK rbn3_span (AF_both3_reac_box_name + RBN_L3J).
      { rbn3_awr. }
      rbn3_upd KEEP GROW.
      lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssc (restrict _ ?msc) |- _ =>
        prreg HS (26%bv : bv 5) R26; prreg HS (20%bv : bv 5) R20; prreg HS (24%bv : bv 5) R24;
        pose proof (regs_kept_of_st_ok_pi Ex _ _ regs _ rbn3h_kl HS ltac:(env_agree_chain HAE)
          ltac:(vm_compute; reflexivity)) as HK;
        cbn [ms_regs restrict] in HK;
        pmkst HS;
        apply SRr_ret; unfold rbn3h_post; split; [reflexivity|];
        exists (ms_regs msc), (ms_mem msc);
        lazymatch goal with |- context [mkCfg _ ?mdx] => exists mdx end
      end.
      split; [first [exact HJ | apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ]|].
      split; [rbn3_keep_all KEEP|]. split; [exact GROW|].
      split; [exact (rbn3_keep_pin regs _ H20 H24 R20 R24 HK)|].
      change ((45 =? 45) && negb false) with true. cbv iota.
      split; [unfold cfg_at, w64; replace (BASE + AF_both3_reac_box_name + RBN_L3J) with (BASE + 15200)
                by (unfold AF_both3_reac_box_name, RBN_L3J; lia); reflexivity|].
      rewrite R26. reflexivity.
Qed.
Definition rbn3j_ss : sstate :=
  mkSS (AF_both3_reac_box_name + RBN_L3J) sr_atoms
    [ YP09.mkRegion (Some 9%nat) 168 176 168 168 [YP09.mkChunk 168 (CVal 8 (SOff 32 0))] ] None
    (mkFacts [ (21%nat, mkAF 0 22 0); (32%nat, mkAF 1 23 0) ] [] []).
Definition rbn3j_E (regs : bvmap 5 word) (len : Z) : env := Eimg (Ereg regs (map (Z_to_bv 64) [len])).
Lemma rbn3j_entry : forall (fq : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) memc i len sp,
  getr regs 21 = w64 i -> getr regs 9 = w64 sp -> 0 <= i <= 22 -> 1 <= len <= 23 -> 0 <= sp -> sp + 176 <= 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) memc) (sp + 168) 8 len ->
  st_ok_pi SEGS VAL (rbn3j_E regs len) rbn3j_ss
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L3J))) memc (seg_rom SEGS))).
Proof.
intros fq W regs memc i len sp H21 H9 Hi Hl Hsp Hsp2 Vl.
rewrite restrict_mkst_fx.
assert (EL : forall m, (m < A_TEXT)%nat -> ew (rbn3j_E regs len) m = ew (Ereg regs (map (Z_to_bv 64) [len])) m)
  by (intros m Hm; unfold rbn3j_E; apply Eimg_low; exact Hm).
assert (E9 : ew (rbn3j_E regs len) 9 = Z_to_bv 64 sp)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E21 : ew (rbn3j_E regs len) 21 = Z_to_bv 64 i)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact H21).
assert (E32 : ew (rbn3j_E regs len) 32 = Z_to_bv 64 len)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (HR : regs_ok (rbn3j_E regs len) sr_atoms regs) by (unfold rbn3j_E; apply regs_ok_Eimg_Ereg).
remember (rbn3j_E regs len) as E eqn:HE. clear HE EL.
unfold rbn3j_ss. apply pa_entry_st_ok_full.
- exact HR.
- vm_compute. reflexivity.
- constructor; [|constructor]; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  cbn [base_val]. rewrite E9, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ sp 168 8 (SOff 32 0) len);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact Vl].
- apply pairwise_disjoint_of_extents.
  unfold extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  cbn [zpairwise_disjoint zall_disjoint]. tauto.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E21, E32, !unsigned_lit_small by lia.
  change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
Qed.
Definition rbn3j_post (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS)
  (memc : word -> option byte) k (regs : bvmap 5 word) (i len : Z) : world SEGS -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md',
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k /\
    (forall a, aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) /\
    mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) mem') /\
    rbn_keep_regs regs regs' rbn3j_cl /\ getr regs' 21 = w64 (i + 1) /\
    c' = cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + (if i + 1 <? len then RBN_L3 else RBN_L3X))
      regs' mem' md'.
Ltac rbn3_join_leaf HJ KEEP GROW HAE E21 :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssc (restrict _ ?msc) |- _ =>
  let R21 := fresh "R21" in let HK := fresh "HK" in
  prreg HS (21%bv : bv 5) R21;
  pose proof (regs_kept_of_st_ok_pi Ex _ _ _ _ rbn3j_kl HS ltac:(env_agree_chain HAE)
    ltac:(vm_compute; reflexivity)) as HK;
  cbn [ms_regs restrict] in HK;
  pmkst HS;
  apply SRr_ret; unfold rbn3j_post; split; [reflexivity|];
  exists (ms_regs msc), (ms_mem msc);
  lazymatch goal with |- context [mkCfg _ ?mdx] => exists mdx end;
  split; [first [exact HJ | apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ]|];
  split; [rbn3_keep_all KEEP|]; split; [exact GROW|];
  split; [exact (rbn3_keep_of_bv _ _ rbn3j_cl rbn3j_kl HK rbn3j_cover)|];
  split; [rewrite R21; rewrite ?ew_ewset_other by lia; rewrite ?E21, ?unsigned_lit_small by lia; unfold w64;
          first [reflexivity | f_equal; lia]|]
  end.
Lemma rbn3_join : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
  (regs : bvmap 5 word) i len,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 21 = w64 i -> getr regs 9 = getr regs 2 -> spZ regs + 176 <= 2 ^ 64 ->
  0 <= i <= 22 -> 1 <= len <= 23 ->
  val_mem SEGS (mrestrict (w_H W) memc) (spZ regs + 168) 8 len ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + RBN_L3J) regs memc mdc)
    (rbn3j_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs i len).
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs i len HJ H21 H9 Hsp Hi Hl Vl.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof (@paj_run fq _ _ _ _ _ B LAWS) as RUN.
pose proof (@paj_run_to fq _ _ _ _ _ B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
assert (Hsp0 : 0 <= spZ regs) by (unfold spZ; pose proof (bv_unsigned_in_range 64 (getr regs 2)); lia).
assert (H9' : getr regs 9 = w64 (spZ regs)) by (rewrite H9; unfold w64, spZ; symmetry; apply Z_to_bv_bv_unsigned).
pose proof (rbn3j_entry fq W regs memc i len (spZ regs) H21 H9' Hi Hl Hsp0 Hsp Vl) as HS.
assert (E21 : ew (rbn3j_E regs len) 21 = Z_to_bv 64 i)
  by (unfold rbn3j_E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact H21).
assert (E32 : ew (rbn3j_E regs len) 32 = Z_to_bv 64 len)
  by (unfold rbn3j_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
set (E := rbn3j_E regs len) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, rbn3j_E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (map (Z_to_bv 64) [len])) E)
  by (unfold E, rbn3j_E; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (SHOK : sh_ok SEGS rbn3_B [] E (mrestrict (w_H W) memc)) by constructor.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) memc a)
  by (intros; reflexivity).
assert (GROW : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) memc)) by apply mem_grows_refl.
unfold cfg_at. rewrite <- Z.add_assoc.
paj_run_tok RUN HS HJ SHOK rbn3_span.
{ rbn3_awr. }
rbn3_upd KEEP GROW.
psrr_branch_tok RUN BR HS SHOK rbn3_span.
- rewrite branch_ltu_U in Hc.
  rewrite (U_atom_off _ 21 i 1) in Hc by first [lia | rewrite ?ew_ewset_other by lia; assumption].
  rbn3_U Hc 32%nat len. apply Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK rbn3_span (AF_both3_reac_box_name + RBN_L3).
  { rbn3_awr. }
  rbn3_upd KEEP GROW.
  rbn3_join_leaf HJ KEEP GROW HAE E21.
  replace (i + 1 <? len) with true by (symmetry; apply Z.ltb_lt; lia).
  change (if true then RBN_L3 else RBN_L3X) with RBN_L3.
  unfold cfg_at, w64. replace (BASE + AF_both3_reac_box_name + RBN_L3) with (BASE + 15124)
    by (unfold AF_both3_reac_box_name, RBN_L3; lia). reflexivity.
- rewrite branch_ltu_U in Hc.
  rewrite (U_atom_off _ 21 i 1) in Hc by first [lia | rewrite ?ew_ewset_other by lia; assumption].
  rbn3_U Hc 32%nat len. apply Z.ltb_ge in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK rbn3_span (AF_both3_reac_box_name + RBN_L3X).
  { rbn3_awr. }
  rbn3_upd KEEP GROW.
  rbn3_join_leaf HJ KEEP GROW HAE E21.
  replace (i + 1 <? len) with false by (symmetry; apply Z.ltb_ge; lia).
  change (if false then RBN_L3 else RBN_L3X) with RBN_L3X.
  unfold cfg_at, w64. replace (BASE + AF_both3_reac_box_name + RBN_L3X) with (BASE + 15228)
    by (unfold AF_both3_reac_box_name, RBN_L3X; lia). reflexivity.
Qed.
Lemma rbn3_shadow_band : forall x, 0 <= x < 2 ^ 47 -> SHADOW_OFF <= shadow_addr x < kHighMemBeg.
Proof.
intros x Hx. unfold shadow_addr, SHADOW_OFF, kHighMemBeg.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_lt_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma rbn3_app_not_shadow : forall lo len x y,
  in_app lo len -> lo <= x < lo + len -> 0 <= y < 2 ^ 47 -> x <> shadow_addr y.
Proof.
intros lo len x y Happ Hx Hy.
pose proof (rbn3_shadow_band y Hy) as Hb.
pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)) as CR. unfold YG0f.ASAN_CEIL in CR.
unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, YG0f.ASAN_CEIL in *. lia.
Qed.
Lemma rbn3_kept_mono : forall lyc1 Sc1 (W1 : world SEGS) m1 (W2 : world SEGS) m2 sp (E1 E2 : Z -> Prop),
  (forall a, E1 a -> E2 a) -> tsb_ch_kept B lyc1 Sc1 W1 m1 W2 m2 sp E1 ->
  tsb_ch_kept B lyc1 Sc1 W1 m1 W2 m2 sp E2.
Proof.
intros lyc1 Sc1 W1 m1 W2 m2 sp E1 E2 HE (K1 & K2 & K3 & K4 & K5 & K6).
split; [intros a Ha Hw Hn; exact (K1 a Ha Hw ltac:(intros X; exact (Hn (HE a X))))|].
split; [intros b m j Hin Hj Hn; exact (K2 b m j Hin Hj ltac:(intros X; exact (Hn (HE _ X))))|].
split; [exact K3|].
split; [intros cid pos a Hin Hr Hn; exact (K4 cid pos a Hin Hr ltac:(intros X; exact (Hn (HE a X))))|].
split; [exact K5 | exact K6].
Qed.
Lemma rbn3_kept_refl : forall lyc1 Sc1 (W1 : world SEGS) m1 sp (E : Z -> Prop),
  (forall a, sp - TSB_CH_STK <= a < sp -> apresent (w_H W1) m1 a) ->
  tsb_ch_kept B lyc1 Sc1 W1 m1 W1 m1 sp E.
Proof.
intros lyc1 Sc1 W1 m1 sp E Hp.
split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
split; [intros; reflexivity|]. split; [intros a _ _ H; exact H | exact Hp].
Qed.
Lemma rbn3_kept_trans : forall lyc1 Sc1 lyc2 Sc2 (W1 : world SEGS) m1 (W2 : world SEGS) m2 (W3 : world SEGS) m3 sp
  (E1 E2 E3 : Z -> Prop),
  tsb_ch_kept B lyc1 Sc1 W1 m1 W2 m2 sp E1 -> tsb_ch_kept B lyc2 Sc2 W2 m2 W3 m3 sp E2 ->
  ablocks B lyc2 Sc2 = ablocks B lyc1 Sc1 -> frames Sc2 = frames Sc1 ->
  (forall cid pos, frame_addr lyc2 cid pos = frame_addr lyc1 cid pos) ->
  (forall a, E1 a -> E3 a) -> (forall a, E2 a -> E3 a) ->
  tsb_ch_kept B lyc1 Sc1 W1 m1 W3 m3 sp E3.
Proof.
intros lyc1 Sc1 lyc2 Sc2 W1 m1 W2 m2 W3 m3 sp E1 E2 E3
  (A1 & A2 & A3 & A4 & A5 & A6) (C1 & C2 & C3 & C4 & C5 & C6) HB HFs HFa HE1 HE2.
split.
{ intros a Ha Hw Hn. rewrite (C1 a Ha Hw ltac:(intros X; exact (Hn (HE2 a X)))).
  exact (A1 a Ha Hw ltac:(intros X; exact (Hn (HE1 a X)))). }
split.
{ intros b m j Hin Hj Hn. rewrite (C2 b m j ltac:(rewrite HB; exact Hin) Hj ltac:(intros X; exact (Hn (HE2 _ X)))).
  exact (A2 b m j Hin Hj ltac:(intros X; exact (Hn (HE1 _ X)))). }
split.
{ intros a Hi Ho He. rewrite (C3 a Hi Ho He). exact (A3 a Hi Ho He). }
split.
{ intros cid pos a Hin Hr Hn.
  rewrite (C4 cid pos a ltac:(rewrite HFs; exact Hin)
    ltac:(unfold frame_rng in *; cbn [fst snd] in *; rewrite (HFa cid pos); exact Hr)
    ltac:(intros X; exact (Hn (HE2 a X)))).
  exact (A4 cid pos a Hin Hr ltac:(intros X; exact (Hn (HE1 a X)))). }
split; [intros a Ha Hw Hp; apply C5; [exact Ha | exact Hw | exact (A5 a Ha Hw Hp)] | exact C6].
Qed.
Lemma rbn3_fa_eq : forall STK sp0 FP ly S W0 mem0 md0 own lyc1 Sc1 (W1 : world SEGS) m1 md1 k1
  lyc2 Sc2 (W2 : world SEGS) m2 md2 k2,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc1 Sc1 W1 m1 md1 k1 ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc2 Sc2 W2 m2 md2 k2 ->
  forall cid pos, frame_addr lyc2 cid pos = frame_addr lyc1 cid pos.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc1 Sc1 W1 m1 md1 k1 lyc2 Sc2 W2 m2 md2 k2 J1 J2 cid pos.
pose proof J1 as (_ & (_ & _ & _ & _ & _ & F1 & _) & _).
pose proof J2 as (_ & (_ & _ & _ & _ & _ & F2 & _) & _).
unfold frame_addr. rewrite F1, F2. reflexivity.
Qed.
Lemma rbn3_awr_tr : forall STK sp0 FP bl0 blc lyc1 lyc2 own a,
  (forall cid pos, frame_addr lyc2 cid pos = frame_addr lyc1 cid pos) ->
  awr_byte STK sp0 FP bl0 blc lyc1 own a -> awr_byte STK sp0 FP bl0 blc lyc2 own a.
Proof.
intros STK sp0 FP bl0 blc lyc1 lyc2 own a HFa [H | [H | [H | (cid & pos & Hin & Hr)]]];
  [left; exact H | right; left; exact H | right; right; left; exact H|].
right; right; right. exists cid, pos. split; [exact Hin|].
unfold in_zr, shadow_addr in *. rewrite (HFa cid pos). exact Hr.
Qed.
Lemma rbn3_band_eq : forall lyc1 Sc1 (W1 : world SEGS) m1 (W2 : world SEGS) m2 sp (E : Z -> Prop) a,
  tsb_ch_kept B lyc1 Sc1 W1 m1 W2 m2 sp E ->
  alloc_ceiling <= sp - TSB_CH_STK ->
  (forall b, E b -> alloc_ceiling <= b \/ (exists lo len, in_app lo len /\ lo <= b < lo + len)) ->
  SHADOW_OFF - 8 <= a < kHighMemBeg ->
  aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a.
Proof.
intros lyc1 Sc1 W1 m1 W2 m2 sp E a HK Hsp HE Ha.
pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)) as CR. unfold YG0f.ASAN_CEIL in CR.
apply (proj1 HK); [unfold kHighMemBeg, SHADOW_OFF in *; lia | unfold kHighMemBeg, SHADOW_OFF in *; lia|].
intros HEa. destruct (HE _ HEa) as [Hc | (lo & len & Happ & Hin)].
- unfold kHighMemBeg in *. lia.
- unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, YG0f.ASAN_CEIL in *. lia.
Qed.
Lemma rbn3_ra_keep : forall (rd rd' : Z -> option Z) a n,
  (forall s, SHADOW_OFF - 8 <= s < kHighMemBeg -> rd' s = rd s) ->
  0 <= a -> a + n <= 2 ^ 47 -> range_addressable rd SHADOW_OFF a n -> range_addressable rd' SHADOW_OFF a n.
Proof.
intros rd rd' a n Heq Ha Han HR x Hx. destruct (HR x Hx) as (s & Hs & Hok).
exists s. split; [|exact Hok]. change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x).
rewrite (Heq (shadow_addr x) ltac:(pose proof (rbn3_shadow_band x ltac:(lia)); lia)).
change (shadow_addr x) with (shadow_of_addr SHADOW_OFF x). exact Hs.
Qed.
Lemma rbn3_val_keep : forall (H H' : word -> bool) (m m' : word -> option byte) a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview SEGS H' m' x = aview SEGS H m x) ->
  val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H' m') a n v.
Proof.
intros Hh Hh' m m' a n v Heq HV j Hj.
rewrite (mbyte_of_aview SEGS Hh Hh' m m' (a + Z.of_nat j) (Heq (a + Z.of_nat j) ltac:(lia))).
exact (HV j Hj).
Qed.
Lemma rbn3_ro_keep : forall lyc1 Sc1 (W1 : world SEGS) m1 (W2 : world SEGS) m2 sp E,
  tsb_ch_kept B lyc1 Sc1 W1 m1 W2 m2 sp E ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W1) m1) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) m2).
Proof.
intros lyc1 Sc1 W1 m1 W2 m2 sp E (_ & _ & K3 & _) HRO a Hro Ho He.
rewrite (K3 a ltac:(destruct Hro as [(s & Hs & _ & Hr) | Hgot];
  [exists s; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hgot)]) Ho He).
exact (HRO a Hro Ho He).
Qed.
Lemma rbn3_kept_same : forall lyc1 Sc1 (W1 : world SEGS) m1 (W2 : world SEGS) m2 m3 sp E,
  tsb_ch_kept B lyc1 Sc1 W1 m1 W2 m2 sp E ->
  (forall a, aview SEGS (w_H W2) m3 a = aview SEGS (w_H W2) m2 a) ->
  mem_grows (mrestrict (w_H W2) m2) (mrestrict (w_H W2) m3) ->
  tsb_ch_kept B lyc1 Sc1 W1 m1 W2 m3 sp E.
Proof.
intros lyc1 Sc1 W1 m1 W2 m2 m3 sp E (K1 & K2 & K3 & K4 & K5 & K6) Hav Hgr.
split; [intros a Ha Hw Hn; rewrite (Hav a); exact (K1 a Ha Hw Hn)|].
split; [intros b m j Hin Hj Hn; rewrite (Hav (b + j)); exact (K2 b m j Hin Hj Hn)|].
split; [intros a Hi Ho He; rewrite (Hav a); exact (K3 a Hi Ho He)|].
split; [intros cid pos a Hin Hr Hn; rewrite (Hav a); exact (K4 cid pos a Hin Hr Hn)|].
split; [intros a Ha Hw Hp; apply (apresent_grows _ _ _ _ Hgr); exact (K5 a Ha Hw Hp)
       | intros a Ha; apply (apresent_grows _ _ _ _ Hgr); exact (K6 a Ha)].
Qed.
Lemma rbn3_kr_comp : forall (ra rb rz : bvmap 5 word) (cla clb cl : list Z),
  rbn_keep_regs ra rb cla -> rbn_keep_regs rb rz clb ->
  (forall x, 0 <= x < 32 -> ~ In x cl -> ~ In x cla /\ ~ In x clb) ->
  rbn_keep_regs ra rz cl.
Proof.
intros ra rb rz cla clb cl H1 H2 Hs r Hr Hn. destruct (Hs r Hr Hn) as [Ha Hb].
rewrite (H2 r Hr Hb). exact (H1 r Hr Ha).
Qed.
Lemma rbn3_pres_keep : forall (ra rb : bvmap 5 word), aregs_preserved ra rb -> rbn_keep_regs ra rb rbn_clc.
Proof.
intros ra rb HP r Hr Hn. destruct (Z.eq_dec r 0) as [-> | Hr0]; [reflexivity|].
apply HP. unfold acallee_saved. unfold rbn_clc in Hn. cbn in Hn. lia.
Qed.
Lemma rbn3_hull_sub : forall rd x n a m,
  shadow_hull_vis rd x n -> x <= a -> a + m <= x + n -> 0 < m -> shadow_hull_vis rd a m.
Proof.
intros rd x n a m H Hxa Ham Hm s Hs. apply H. unfold shadow_addr in *.
pose proof (Z.div_le_mono x a 8 ltac:(lia) Hxa) as D1.
pose proof (Z.div_le_mono (a + m - 1) (x + n - 1) 8 ltac:(lia) ltac:(lia)) as D2.
assert (D3 : (SHADOW_OFF + x / 8) / 8 <= (SHADOW_OFF + a / 8) / 8) by (apply Z.div_le_mono; lia).
assert (D4 : (SHADOW_OFF + (a + m - 1) / 8) / 8 <= (SHADOW_OFF + (x + n - 1) / 8) / 8) by (apply Z.div_le_mono; lia).
lia.
Qed.
Lemma rbn3_hull_rng : forall x n s, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> SHADOW_OFF - 8 <= s < kHighMemBeg.
Proof.
intros x n s Hx Hn Hxn Hs.
pose proof (rbn3_shadow_band x ltac:(lia)) as B1.
pose proof (rbn3_shadow_band (x + n - 1) ltac:(lia)) as B2.
pose proof (Z.mul_div_le (shadow_addr x) 8 ltac:(lia)) as M1.
pose proof (Z.mul_div_le (shadow_addr (x + n - 1)) 8 ltac:(lia)) as M2.
assert (M3 : (shadow_addr (x + n - 1) / 8 * 8) mod 8 = 0) by (apply Z_mod_mult).
unfold kHighMemBeg in *. lia.
Qed.
Lemma rbn3_sv_keep : forall (rd rd' : Z -> option Z) x n,
  (forall s, SHADOW_OFF - 8 <= s < kHighMemBeg -> rd' s = rd s) ->
  0 <= x -> 0 < n -> x + n <= 2 ^ 47 -> shadow_hull_vis rd x n -> shadow_hull_vis rd' x n.
Proof.
intros rd rd' x n Heq Hx Hn Hxn HV s Hs.
rewrite (Heq s (rbn3_hull_rng x n s Hx Hn Hxn Hs)). exact (HV s Hs).
Qed.
Lemma rbn3_nth_skipn : forall (xs : list Z) i c r, skipn i xs = c :: r -> nth i xs 0 = c.
Proof.
induction xs as [|x t IH]; intros i c r Hs; destruct i as [|i]; cbn in Hs |- *; try discriminate.
- injection Hs as <- _. reflexivity.
- exact (IH i c r Hs).
Qed.
Hypothesis TSB : tsb_ch_spec B.
Section l.
Variable fq : YK11.FPState.
Variables STK sp0 : Z.
Variable FP : list (Z * Z).
Variable ly : alayout.
Variable S : astate.
Variable W0 : world SEGS.
Variable mem0 : word -> option byte.
Variable md0 : Model.
Variable own : list (Z * Z).
Variable lyc : alayout.
Variable Sc : astate.
Variable W : world SEGS.
Variable memc : word -> option byte.
Variable mdc : Model.
Variable k : Z.
Variable regs : bvmap 5 word.
Variables N D : Z.
Variable src : list Z.
Hypothesis HCX : rbn_lcx B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs.
Hypothesis HREC : rbn_lrec B STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 120) D 24 0 0.
Hypothesis HBUF : rbn_lbuf B STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 120) D 24.
Hypothesis HL1 : (1 <= length src)%nat.
Hypothesis HL23 : Z.of_nat (length src) <= 23.
Hypothesis HALL : Forall (fun c => 0 <= c < 256) src.
Hypothesis HSRC : rbn_lsrc W memc N src.
Hypothesis HSEP : rbn_lsep (spZ regs) (spZ regs + 120) D 24 N (Z.of_nat (length src)).
Hypothesis HNS : N + Z.of_nat (length src) <= spZ regs + 152 \/ spZ regs + 180 <= N.
Hypothesis HDS : D + 24 <= spZ regs + 152 \/ spZ regs + 180 <= D.
Hypothesis HVL : val_mem SEGS (mrestrict (w_H W) memc) (spZ regs + 168) 8 (Z.of_nat (length src)).
Hypothesis G20 : getr regs 20 = w64 24.
Hypothesis G21 : getr regs 21 = w64 0.
Hypothesis G24 : getr regs 24 = w64 45.
Hypothesis G26 : getr regs 26 = w64 0.
Hypothesis G27 : getr regs 27 = w64 N.
Lemma rbn3_spf : alloc_ceiling + TSB_CH_STK <= spZ regs /\ spZ regs <= 2 ^ 47 /\ spZ regs mod 16 = 0 /\
  2 ^ 46 <= spZ regs /\ TSB_CH_STK = 4112.
Proof.
pose proof HCX as (HJ0 & _ & _ & _ & _ & _ & Hal & Hslo & Hshi).
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (_ & _ & Hc & Hd & He & Hf & _) & _).
pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)) as CR. unfold YG0f.ASAN_CEIL in CR.
unfold TSB_CH_STK, ESTACK in *.
split; [|split; [|split; [|split]]]; lia.
Qed.
Lemma rbn3_presw : forall lyc1 Sc1 (W1 : world SEGS) m1 md1 k1,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc1 Sc1 W1 m1 md1 k1 ->
  forall a, spZ regs - TSB_CH_STK <= a < spZ regs -> apresent (w_H W1) m1 a.
Proof.
intros lyc1 Sc1 W1 m1 md1 k1 HJ a Ha.
pose proof HCX as (_ & _ & _ & _ & _ & _ & _ & Hslo & Hshi).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A14 & _).
apply A14. lia.
Qed.
Definition rbn3_Er (m : nat) (a : Z) : Prop :=
  spZ regs + 120 + 16 <= a < spZ regs + 120 + 28 \/ D + 0 <= a < D + 0 + Z.of_nat m.
Lemma rbn3_Er_app : forall m a, (m <= 24)%nat -> rbn3_Er m a ->
  alloc_ceiling <= a \/ (exists lo len, in_app lo len /\ lo <= a < lo + len).
Proof.
intros m a Hm Ha. pose proof rbn3_spf as (H1 & _). pose proof HBUF as (_ & _ & Bapp & _).
destruct Ha as [Ha | Ha].
- left. unfold TSB_CH_STK, ESTACK in *. lia.
- right. exists D, 24. split; [exact Bapp | lia].
Qed.
Lemma rbn3_band : forall (W1 : world SEGS) m1 (m : nat) a,
  tsb_ch_kept B lyc Sc W memc W1 m1 (spZ regs) (rbn3_Er m) -> (m <= 24)%nat ->
  SHADOW_OFF - 8 <= a < kHighMemBeg -> aview SEGS (w_H W1) m1 a = aview SEGS (w_H W) memc a.
Proof.
intros W1 m1 m a HK Hm Ha. pose proof rbn3_spf as (H1 & _).
exact (rbn3_band_eq lyc Sc W memc W1 m1 (spZ regs) (rbn3_Er m) a HK
  ltac:(unfold TSB_CH_STK, ESTACK in *; lia) ltac:(intros b Hb; exact (rbn3_Er_app m b Hm Hb)) Ha).
Qed.
Lemma rbn3_kr : forall (regs1 : bvmap 5 word) (n : Z) (rr : bv 5),
  rbn_keep_regs regs regs1 rbn_cl3 -> 0 <= n < 32 -> ~ In n rbn_cl3 -> Z_to_bv 5 n = rr ->
  getr regs1 rr = getr regs rr.
Proof. intros regs1 n rr HK Hn Hin <-. exact (HK n Hn Hin). Qed.
Lemma rbn3_krg : forall (ra rb : bvmap 5 word) cl (n : Z) (rr : bv 5),
  rbn_keep_regs ra rb cl -> 0 <= n < 32 -> ~ In n cl -> Z_to_bv 5 n = rr -> getr rb rr = getr ra rr.
Proof. intros ra rb cl n rr HK Hn Hin <-. exact (HK n Hn Hin). Qed.
Lemma rbn3_sub_h : forall x, 0 <= x < 32 -> ~ In x rbn_cl3 -> ~ In x rbn_cl3 /\ ~ In x rbn3h_cl.
Proof. intros x Hx Hn. split; [exact Hn|]. unfold rbn_cl3, rbn_clc, rbn3h_cl in *. cbn in *. lia. Qed.
Lemma rbn3_sub_j : forall x, 0 <= x < 32 -> ~ In x rbn_cl3 -> ~ In x rbn_cl3 /\ ~ In x rbn3j_cl.
Proof. intros x Hx Hn. split; [exact Hn|]. unfold rbn_cl3, rbn_clc, rbn3j_cl in *. cbn in *. lia. Qed.
Lemma rbn3_sub_c : forall x, 0 <= x < 32 -> ~ In x rbn_cl3 -> ~ In x rbn_cl3 /\ ~ In x rbn_clc.
Proof. intros x Hx Hn. split; [exact Hn|]. unfold rbn_cl3, rbn_clc in *. cbn in *. lia. Qed.
Ltac rbn3_kreg KR n r H :=
  pose proof (rbn3_kr _ n r KR ltac:(lia)
    ltac:(unfold rbn_cl3, rbn_clc; cbn; lia) ltac:(apply bv_eq; vm_compute; reflexivity)) as H.
Lemma rbn3_regs1 : forall (regs1 : bvmap 5 word), rbn_keep_regs regs regs1 rbn_cl3 ->
  getr regs1 2 = getr regs 2 /\ getr regs1 3 = w64 (as_gp B) /\ getr regs1 4 = w64 (as_tp B) /\
  getr regs1 9 = getr regs1 2 /\ getr regs1 20 = w64 24 /\ getr regs1 22 = w64 SHADOW_OFF /\
  getr regs1 24 = w64 45 /\ getr regs1 27 = w64 N /\ spZ regs1 = spZ regs.
Proof.
intros regs1 KR.
pose proof HCX as (_ & _ & Hgp & Htp & H92 & H22 & _ & _ & _).
rbn3_kreg KR 2 (2%bv : bv 5) K2.
rbn3_kreg KR 3 (3%bv : bv 5) K3.
rbn3_kreg KR 4 (4%bv : bv 5) K4.
rbn3_kreg KR 9 (9%bv : bv 5) K9.
rbn3_kreg KR 20 (20%bv : bv 5) K20.
rbn3_kreg KR 22 (22%bv : bv 5) K22.
rbn3_kreg KR 24 (24%bv : bv 5) K24.
rbn3_kreg KR 27 (27%bv : bv 5) K27.
split; [exact K2|]. split; [rewrite K3; exact Hgp|]. split; [rewrite K4; exact Htp|].
split; [rewrite K9, K2; exact H92|]. split; [rewrite K20; exact G20|]. split; [rewrite K22; exact H22|].
split; [rewrite K24; exact G24|]. split; [rewrite K27; exact G27|].
unfold spZ. rewrite K2. reflexivity.
Qed.
Definition rbn3_st (i : Z) (sn : bool) (w : list Z) (lyc1 : alayout) (Sc1 : astate) (W1 : world SEGS)
  (mem1 : word -> option byte) (md1 : Model) (regs1 : bvmap 5 word) : Prop :=
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc1 Sc1 W1 mem1 md1 k /\
  frames Sc1 = frames Sc /\ ablocks B lyc1 Sc1 = ablocks B lyc Sc /\
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W1) mem1) /\
  tsb_ch_kept B lyc Sc W memc W1 mem1 (spZ regs) (rbn3_Er (length w)) /\
  val_mem SEGS (mrestrict (w_H W1) mem1) (spZ regs + 120 + 16) 8 (Z.of_nat (length w)) /\
  val_mem SEGS (mrestrict (w_H W1) mem1) (spZ regs + 120 + 24) 4 0 /\
  garr8 SEGS (mrestrict (w_H W1) mem1) (D + 0) w /\
  rbn_keep_regs regs regs1 rbn_cl3 /\
  getr regs1 21 = w64 i /\ getr regs1 26 = w64 (if sn then 1 else 0) /\ (length w <= 23)%nat.
Lemma rbn3_init : rbn3_st 0 false [] lyc Sc W memc mdc regs.
Proof.
pose proof HCX as (HJ0 & HRO0 & _).
pose proof HREC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Vn & Vov & _).
split; [exact HJ0|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HRO0|].
split; [apply rbn3_kept_refl; exact (rbn3_presw lyc Sc W memc mdc k HJ0)|].
split; [cbn [length]; change (Z.of_nat 0) with 0; exact Vn|].
split; [exact Vov|].
split; [apply garr8_nil|].
split; [intros r Hr Hn; reflexivity|].
split; [exact G21|]. split; [exact G26|]. cbn [length]; lia.
Qed.
Lemma rbn3_exit : forall i (sn : bool) w lyc1 Sc1 (W1 : world SEGS) mem1 md1 regs1,
  w = bn_TK src -> rbn3_st i sn w lyc1 Sc1 W1 mem1 md1 regs1 ->
  rbn_lpost B fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L3X rbn_cl3 (spZ regs + 120) D 0
    (Z.of_nat (length (bn_TK src))) 0 (bn_TK src) W1
    (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + RBN_L3X) regs1 mem1 md1).
Proof.
intros i sn w lyc1 Sc1 W1 mem1 md1 regs1 Hw HST. subst w.
destruct HST as (J1 & HF & HB & HRO & HK & V16 & V24 & HG & KR & _ & _ & _).
exists lyc1, Sc1, regs1, mem1, md1.
split; [reflexivity|]. split; [exact J1|]. split; [exact HF|]. split; [exact HB|]. split; [exact HRO|].
split; [exact KR|]. split; [exact V16|]. split; [exact V24|]. split; [exact HG|]. exact HK.
Qed.
Definition rbn3_POST : world SEGS -> config -> Prop :=
  rbn_lpost B fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L3X rbn_cl3 (spZ regs + 120) D 0
    (Z.of_nat (length (bn_TK src))) 0 (bn_TK src).
Lemma rbn3_cont : forall (i : Z) (sn : bool) (w rr : list Z) lyc1 Sc1 (W2 : world SEGS) mem2 md2 regs2,
  rr = skipn (Z.to_nat (i + 1)) src -> 0 <= i < Z.of_nat (length src) ->
  w ++ bn_tk sn rr = bn_TK src ->
  rbn3_st i sn w lyc1 Sc1 W2 mem2 md2 regs2 ->
  (forall i2 (sn2 : bool) w2 lyc2 Sc2 (W3 : world SEGS) mem3 md3 regs3,
     rr = skipn (Z.to_nat i2) src -> 0 <= i2 < Z.of_nat (length src) -> w2 ++ bn_tk sn2 rr = bn_TK src ->
     rbn3_st i2 sn2 w2 lyc2 Sc2 W3 mem3 md3 regs3 ->
     SRr SEGS W3 (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + RBN_L3) regs3 mem3 md3) rbn3_POST) ->
  SRr SEGS W2 (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + RBN_L3J) regs2 mem2 md2) rbn3_POST.
Proof.
intros i sn w rr lyc1 Sc1 W2 mem2 md2 regs2 Hrr Hi Hw HST IHc.
pose proof HST as (J1 & HFs & HBl & HRO1 & HK1 & V16 & V24 & HG1 & KR1 & R21 & R26 & Hlw).
destruct (rbn3_regs1 regs2 KR1) as (K2 & K3 & K4 & K9 & K20 & K22 & K24 & K27 & Ksp).
pose proof rbn3_spf as (Hs1 & Hs2 & Hs16 & Hs46 & Hstk).
pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)) as CRc. unfold YG0f.ASAN_CEIL in CRc.
pose proof HBUF as (BD & B63 & Bapp & Bam & Boi & Bsep & Bdis & BRA & BSV & BW).
assert (VLEN : val_mem SEGS (mrestrict (w_H W2) mem2) (spZ regs2 + 168) 8 (Z.of_nat (length src))).
{ rewrite Ksp. apply (rbn3_val_keep (w_H W) (w_H W2) memc mem2 (spZ regs + 168) 8 _); [|exact HVL].
  intros x Hx. apply (proj1 HK1); [lia | lia|]. intros [Hq | Hq]; lia. }
eapply SRr_bind.
{ apply (rbn3_join fq STK sp0 FP ly S W0 mem0 md0 own lyc1 Sc1 W2 mem2 md2 k regs2 i
    (Z.of_nat (length src)) J1 R21 K9 ltac:(rewrite Ksp; lia) ltac:(lia) ltac:(lia) VLEN). }
cbv beta. intros W3 c3 Hwle3 HP3.
destruct HP3 as (HWe & regs3 & mem3 & md3 & J3 & KEEP3 & GROW3 & KR3 & R21' & Hc3).
subst W3. subst c3.
assert (HSTn : rbn3_st (i + 1) sn w lyc1 Sc1 W2 mem3 md3 regs3).
{ split; [exact J3|]. split; [exact HFs|]. split; [exact HBl|].
  split; [intros a H1 H2 H3; rewrite (KEEP3 a); exact (HRO1 a H1 H2 H3)|].
  split; [exact (rbn3_kept_same lyc Sc W memc W2 mem2 mem3 (spZ regs) _ HK1 KEEP3 GROW3)|].
  split; [apply (rbn3_val_keep (w_H W2) (w_H W2) mem2 mem3 _ _ _ ltac:(intros x _; exact (KEEP3 x))); exact V16|].
  split; [apply (rbn3_val_keep (w_H W2) (w_H W2) mem2 mem3 _ _ _ ltac:(intros x _; exact (KEEP3 x))); exact V24|].
  split; [apply (garr8_aview_kept SEGS (w_H W2) (w_H W2) mem2 mem3 (D + 0) w
            ltac:(intros x _; exact (KEEP3 x))); exact HG1|].
  split; [exact (rbn3_kr_comp regs regs2 regs3 rbn_cl3 rbn3j_cl rbn_cl3 KR1 KR3 rbn3_sub_j)|].
  split; [exact R21'|].
  split; [rewrite (rbn3_krg regs2 regs3 rbn3j_cl 26 (26%bv : bv 5) KR3 ltac:(lia)
            ltac:(unfold rbn3j_cl; cbn; lia) ltac:(apply bv_eq; vm_compute; reflexivity)); exact R26|].
  exact Hlw. }
destruct (i + 1 <? Z.of_nat (length src)) eqn:Hlt.
- apply Z.ltb_lt in Hlt.
  exact (IHc (i + 1) sn w lyc1 Sc1 W2 mem3 md3 regs3 Hrr ltac:(lia) Hw HSTn).
- apply Z.ltb_ge in Hlt.
  assert (Hr0 : rr = []) by (rewrite Hrr; apply skipn_all2; lia).
  apply SRr_ret. apply (rbn3_exit (i + 1) sn w lyc1 Sc1 W2 mem3 md3 regs3); [|exact HSTn].
  rewrite Hr0 in Hw. cbn [bn_tk] in Hw. rewrite app_nil_r in Hw. exact Hw.
Qed.
Lemma rbn3_loop : forall (rl : list Z) (i : Z) (sn : bool) (w : list Z) lyc1 Sc1 (W1 : world SEGS) mem1 md1 regs1,
  rl = skipn (Z.to_nat i) src -> 0 <= i < Z.of_nat (length src) -> w ++ bn_tk sn rl = bn_TK src ->
  rbn3_st i sn w lyc1 Sc1 W1 mem1 md1 regs1 ->
  SRr SEGS W1 (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + RBN_L3) regs1 mem1 md1) rbn3_POST.
Proof.
induction rl as [|c rl' IH]; intros i sn w lyc1 Sc1 W1 mem1 md1 regs1 Hrl Hi Hw HST.
{ exfalso. pose proof (length_skipn (Z.to_nat i) src) as HL. rewrite <- Hrl in HL. cbn [length] in HL. lia. }
pose proof HST as (J1 & HFs & HBl & HRO1 & HK1 & V16 & V24 & HG1 & KR1 & R21 & R26 & Hlw).
destruct (rbn3_regs1 regs1 KR1) as (K2 & K3 & K4 & K9 & K20 & K22 & K24 & K27 & Ksp).
pose proof rbn3_spf as (Hs1 & Hs2 & Hs16 & Hs46 & Hstk).
pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)) as CRc. unfold YG0f.ASAN_CEIL in CRc.
pose proof HCX as (HJ0 & HRO0 & Hgp & Htp & H92 & H22 & Hal & Hslo & Hshi).
pose proof HSRC as (SG & SP0 & S63 & S47 & SRA).
pose proof HSEP as (PD & PR & PWn).
pose proof HBUF as (BD & B63 & Bapp & Bam & Boi & Bsep & Bdis & BRA & BSV & BW).
pose proof HREC as (Rp & Rm & R63 & Ram & Roi & Rsep & RD & Rcap & Rn0 & Rn1 & Rov &
  VD & Vcap & Vn0 & Vov0 & RRA & RSV & RW).
pose proof HK1 as (HKa & HKb & HKc & HKd & HKe & HKf).
assert (HAM : spZ regs + 120 + 28 <= 2 ^ 47).
{ unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ram. lia. }
assert (HBM : D + 24 <= 2 ^ 47).
{ unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Bam.
  unfold in_app, kLowShadowBeg, kHighMemBeg in Bapp. lia. }
assert (Hilt : (Z.to_nat i < length src)%nat) by lia.
assert (Hc : nth (Z.to_nat i) src 0 = c) by (apply (rbn3_nth_skipn src (Z.to_nat i) c rl'); symmetry; exact Hrl).
assert (Hcr : 0 <= c < 256) by (rewrite <- Hc; apply (proj1 (Forall_forall _ _) HALL); apply nth_In; exact Hilt).
assert (Hrl' : rl' = skipn (Z.to_nat (i + 1)) src).
{ replace (Z.to_nat (i + 1)) with (1 + Z.to_nat i)%nat by lia.
  rewrite <- skipn_skipn, <- Hrl. reflexivity. }
assert (BANDm : forall s, SHADOW_OFF - 8 <= s < kHighMemBeg ->
  aview SEGS (w_H W1) mem1 s = aview SEGS (w_H W) memc s)
  by (intros s Hs; exact (rbn3_band W1 mem1 (length w) s HK1 ltac:(lia) Hs)).
assert (Vc : val_mem SEGS (mrestrict (w_H W1) mem1) (N + i) 1 c).
{ apply (rbn3_val_keep (w_H W) (w_H W1) memc mem1 (N + i) 1 c).
  - intros x Hx. cbn [Z.of_nat] in Hx. apply HKa; [lia | lia|]. intros [Hq | Hq]; lia.
  - destruct (garr8_nthZ SEGS (mrestrict (w_H W) memc) N src i SG ltac:(lia) ltac:(lia)) as (Hv & _).
    rewrite Hc in Hv. exact Hv. }
assert (HRAc : range_addressable (aview SEGS (w_H W1) mem1) SHADOW_OFF (N + i) 1).
{ apply (rbn3_ra_keep (aview SEGS (w_H W) memc) (aview SEGS (w_H W1) mem1) (N + i) 1 BANDm
    ltac:(lia) ltac:(lia)).
  intros x Hx. apply SRA. lia. }
eapply SRr_bind.
{ apply (rbn3_head fq STK sp0 FP ly S W0 mem0 md0 own lyc1 Sc1 W1 mem1 md1 k regs1 N i c sn J1
    K20 K24 K22 R21 R26 K27 K9 ltac:(rewrite Ksp; lia) ltac:(lia) ltac:(lia) ltac:(lia) Vc Hcr HRAc). }
cbv beta. intros W' c' Hwle HP'.
destruct HP' as (HWe & regs' & mem' & md' & J' & KEEP' & GROW' & KR' & Hrest). subst W'.
assert (KRc : rbn_keep_regs regs regs' rbn_cl3)
  by (exact (rbn3_kr_comp regs regs1 regs' rbn_cl3 rbn3h_cl rbn_cl3 KR1 KR' rbn3_sub_h)).
destruct (rbn3_regs1 regs' KRc) as (K2' & K3' & K4' & K9' & K20' & K22' & K24' & K27' & Ksp').
assert (R21' : getr regs' 21 = w64 i).
{ rewrite (rbn3_krg regs1 regs' rbn3h_cl 21 (21%bv : bv 5) KR' ltac:(lia)
    ltac:(unfold rbn3h_cl; cbn; lia) ltac:(apply bv_eq; vm_compute; reflexivity)). exact R21. }
assert (HRO' : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W1) mem'))
  by (intros a H1 H2 H3; rewrite (KEEP' a); exact (HRO1 a H1 H2 H3)).
assert (HK' : tsb_ch_kept B lyc Sc W memc W1 mem' (spZ regs) (rbn3_Er (length w)))
  by (exact (rbn3_kept_same lyc Sc W memc W1 mem1 mem' (spZ regs) _ HK1 KEEP' GROW')).
assert (BANDe : forall s, SHADOW_OFF - 8 <= s < kHighMemBeg ->
  aview SEGS (w_H W1) mem' s = aview SEGS (w_H W) memc s)
  by (intros s Hs; rewrite (KEEP' s); exact (BANDm s Hs)).
assert (HFa : forall cid pos, frame_addr lyc1 cid pos = frame_addr lyc cid pos)
  by (exact (rbn3_fa_eq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k lyc1 Sc1 W1 mem1 md1 k HJ0 J1)).
case_eq ((c =? 45) && negb sn); intros Hb; rewrite Hb in Hrest; cbv iota in Hrest.
- apply andb_true_iff in Hb. destruct Hb as (Hb1 & Hb2). apply Z.eqb_eq in Hb1.
  destruct sn; [cbn in Hb2; discriminate Hb2|].
  destruct Hrest as (Hc' & R26'). subst c'.
  apply (rbn3_cont i true w rl' lyc1 Sc1 W1 mem' md' regs'); [exact Hrl' | exact Hi | | | exact IH].
  + rewrite <- Hw. f_equal. rewrite bn_tk_cons, Hb1. reflexivity.
  + split; [exact J'|]. split; [exact HFs|]. split; [exact HBl|]. split; [exact HRO'|].
    split; [exact HK'|].
    split; [apply (rbn3_val_keep (w_H W1) (w_H W1) mem1 mem' _ _ _ ltac:(intros x _; exact (KEEP' x))); exact V16|].
    split; [apply (rbn3_val_keep (w_H W1) (w_H W1) mem1 mem' _ _ _ ltac:(intros x _; exact (KEEP' x))); exact V24|].
    split; [apply (garr8_aview_kept SEGS (w_H W1) (w_H W1) mem1 mem' (D + 0) w
              ltac:(intros x _; exact (KEEP' x))); exact HG1|].
    split; [exact KRc|]. split; [exact R21'|]. split; [exact R26'|]. exact Hlw.
- destruct Hrest as (Hc' & R1' & R10' & R11' & R26'). subst c'.
  assert (Htk : bn_tk sn (c :: rl') = rbn_lc c :: bn_tk sn rl') by (rewrite bn_tk_cons, Hb; reflexivity).
  rewrite Htk in Hw.
  assert (Hw' : (w ++ [rbn_lc c]) ++ bn_tk sn rl' = bn_TK src)
    by (rewrite <- app_assoc; cbn [app]; exact Hw).
  assert (Hlen1 : (length w + 1 <= 23)%nat).
  { assert (HL : (length w + 1 + length (bn_tk sn rl') = length (bn_TK src))%nat)
      by (rewrite <- Hw'; rewrite !length_app; cbn [length]; lia).
    pose proof (bn_tk_len src false) as HB2. unfold bn_TK in HL. lia. }
  pose proof (rbn_lc_range c Hcr) as Hlcr.
  eapply SRr_bind.
  { apply (TSB fq STK sp0 FP ly S W0 mem0 md0 own lyc1 Sc1 W1 mem' md' k regs'
      (spZ regs + 120) (rbn_lc c) D 24 (Z.of_nat (length w)) []).
    - exact J'.
    - exact HRO'.
    - rewrite R1'. unfold w64.
      replace (BASE + AF_both3_reac_box_name + RBN_L3J) with (BASE + 15200)
        by (unfold AF_both3_reac_box_name, RBN_L3J; lia).
      apply ret_ok_codeptr_v; [lia | reflexivity].
    - unfold raZ. rewrite R1'. unfold w64.
      pose proof pa_B_ok as (HB0 & HB1 & HB2). pose proof pa_base_lo as HBL.
      unfold YImgTop.IMG_LO in HBL. unfold AF_both3_reac_box_name, RBN_L3J in *.
      rewrite unsigned_lit_small by lia. lia.
    - exact K3'.
    - exact K4'.
    - rewrite R10', Ksp. reflexivity.
    - exact R11'.
    - apply achain_low. unfold s0Z. rewrite getr_same by reg_neq_tac.
      rewrite unsigned_lit_small by lia. lia.
    - rewrite Ksp'. lia.
    - rewrite Ksp'. exact Hslo.
    - rewrite Ksp'. exact Hshi.
    - lia.
    - lia.
    - lia.
    - exact R63.
    - exact Ram.
    - rewrite Ksp'. left. lia.
    - exact Roi.
    - lia.
    - lia.
    - lia.
    - apply (rbn3_val_keep (w_H W) (w_H W1) memc mem' (spZ regs + 120) 8 D); [|exact VD].
      intros x Hx. rewrite (KEEP' x). apply HKa; [lia | lia|]. intros [Hq | Hq]; lia.
    - apply (rbn3_val_keep (w_H W) (w_H W1) memc mem' (spZ regs + 120 + 8) 8 24); [|exact Vcap].
      intros x Hx. rewrite (KEEP' x). apply HKa; [lia | lia|]. intros [Hq | Hq]; lia.
    - apply (rbn3_val_keep (w_H W1) (w_H W1) mem1 mem' _ _ _ ltac:(intros x _; exact (KEEP' x))). exact V16.
    - apply (rbn3_ra_keep (aview SEGS (w_H W) memc) (aview SEGS (w_H W1) mem') (spZ regs + 120) 28 BANDe
        ltac:(lia) ltac:(lia) RRA).
    - apply (rbn3_sv_keep (aview SEGS (w_H W) memc) (aview SEGS (w_H W1) mem') (spZ regs + 120) 28 BANDe
        ltac:(lia) ltac:(lia) ltac:(lia) RSV).
    - intros a Ha. split.
      + rewrite HBl. apply (rbn3_awr_tr STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc lyc1 own a HFa).
        exact (proj1 (RW a Ha)).
      + apply (apresent_grows _ _ _ _ GROW'). apply HKe; [lia | lia|]. exact (proj2 (RW a Ha)).
    - intros Hcap. split; [lia|]. split; [lia|].
      split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia|].
      split.
      { apply (rbn3_ra_keep (aview SEGS (w_H W) memc) (aview SEGS (w_H W1) mem')
          (D + Z.of_nat (length w)) 1 BANDe ltac:(lia) ltac:(lia)).
        intros x Hx. apply BRA. lia. }
      split.
      { apply (rbn3_sv_keep (aview SEGS (w_H W) memc) (aview SEGS (w_H W1) mem')
          (D + Z.of_nat (length w)) 1 BANDe ltac:(lia) ltac:(lia) ltac:(lia)).
        apply (rbn3_hull_sub _ D 24); [exact BSV | lia | lia | lia]. }
      split; [lia|].
      split; [unfold off_img in *; lia|].
      split; [lia|].
      split.
      { rewrite HBl. apply (rbn3_awr_tr STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc lyc1 own _ HFa).
        exact (proj1 (BW (D + Z.of_nat (length w)) ltac:(lia))). }
      apply (apresent_transfer SEGS (w_H W) (w_H W1) memc mem' (D + Z.of_nat (length w)) ltac:(lia)).
      + intros Hi2. pose proof (pa_img_range _ Hi2) as HIR.
        unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in *. lia.
      + rewrite (KEEP' (D + Z.of_nat (length w))). apply HKa; [lia | lia|]. intros [Hq | Hq]; lia.
      + exact (proj2 (BW (D + Z.of_nat (length w)) ltac:(lia))). }
  cbv beta. intros W2 c2 Hwle2 HP2.
  destruct HP2 as (ly2 & S2 & regs2 & mem2 & md2 & Hc2 & J2 & HPr2 & HFs2 & HBl2 & Hcase).
  destruct Hcase as [(Hbad & _) | (Hok & Vn1 & Vb1 & HKcall)]; [exfalso; lia|].
  rewrite R1' in Hc2. subst c2.
  assert (KRp : rbn_keep_regs regs' regs2 rbn_clc) by (exact (rbn3_pres_keep regs' regs2 HPr2)).
  assert (KRn : rbn_keep_regs regs regs2 rbn_cl3)
    by (exact (rbn3_kr_comp regs regs' regs2 rbn_cl3 rbn_clc rbn_cl3 KRc KRp rbn3_sub_c)).
  assert (Hlennat : (length (w ++ [rbn_lc c]) = length w + 1)%nat)
    by (rewrite length_app; cbn [length]; lia).
  assert (Hlenw : Z.of_nat (length (w ++ [rbn_lc c])) = Z.of_nat (length w) + 1)
    by (rewrite Hlennat; lia).
  apply (rbn3_cont i sn (w ++ [rbn_lc c]) rl' ly2 S2 W2 mem2 md2 regs2);
    [exact Hrl' | exact Hi | exact Hw' | | exact IH].
  split; [exact J2|]. split; [rewrite HFs2; exact HFs|]. split; [rewrite HBl2; exact HBl|].
  split; [exact (rbn3_ro_keep lyc1 Sc1 W1 mem' W2 mem2 (spZ regs') _ HKcall HRO')|].
  split.
  { apply (rbn3_kept_trans lyc Sc lyc1 Sc1 W memc W1 mem' W2 mem2 (spZ regs)
      (rbn3_Er (length w)) _ _ HK' ltac:(rewrite <- Ksp'; exact HKcall) HBl HFs HFa).
    - intros a Ha. unfold rbn3_Er in Ha |- *. rewrite Hlennat.
      destruct Ha as [Hq | Hq]; [left; exact Hq | right; lia].
    - intros a Ha. unfold rbn3_Er. rewrite Hlennat.
      destruct Ha as [Hq | Hq]; [left; lia | right; lia]. }
  split; [rewrite Hlenw; exact Vn1|].
  split.
  { apply (rbn3_val_keep (w_H W1) (w_H W2) mem' mem2 (spZ regs + 120 + 24) 4 0).
    - intros x Hx. apply (proj1 HKcall); [lia | rewrite Ksp'; lia|]. intros [Hq | Hq]; lia.
    - apply (rbn3_val_keep (w_H W1) (w_H W1) mem1 mem' _ _ _ ltac:(intros x _; exact (KEEP' x))). exact V24. }
  split.
  { apply (garr8_app1 SEGS (mrestrict (w_H W1) mem') (mrestrict (w_H W2) mem2) (D + 0) w (rbn_lc c)).
    - apply (garr8_aview_kept SEGS (w_H W1) (w_H W1) mem1 mem' (D + 0) w
        ltac:(intros x _; exact (KEEP' x))). exact HG1.
    - replace (D + 0 + Z.of_nat (length w)) with (D + Z.of_nat (length w)) by lia.
      rewrite (Z.mod_small (rbn_lc c) 256) in Vb1 by lia. exact Vb1.
    - lia.
    - intros a Ha. apply (mbyte_of_aview SEGS (w_H W1) (w_H W2) mem' mem2).
      apply (proj1 HKcall); [lia | rewrite Ksp'; lia|]. intros [Hq | Hq]; lia. }
  split; [exact KRn|].
  split.
  { rewrite (rbn3_krg regs' regs2 rbn_clc 21 (21%bv : bv 5) KRp ltac:(lia)
      ltac:(unfold rbn_clc; cbn; lia) ltac:(apply bv_eq; vm_compute; reflexivity)). exact R21'. }
  split.
  { rewrite (rbn3_krg regs' regs2 rbn_clc 26 (26%bv : bv 5) KRp ltac:(lia)
      ltac:(unfold rbn_clc; cbn; lia) ltac:(apply bv_eq; vm_compute; reflexivity)).
    rewrite R26'. exact R26. }
  rewrite length_app. cbn [length]. lia.
Qed.
Lemma rbn3_run : SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + RBN_L3) regs memc mdc)
  rbn3_POST.
Proof.
apply (rbn3_loop src 0 false [] lyc Sc W memc mdc regs).
- cbn [Z.to_nat skipn]. reflexivity.
- lia.
- cbn [app]. unfold bn_TK. reflexivity.
- exact rbn3_init.
Qed.
End l.
Theorem rbn_l3_fits : rbn_L3_fits B.
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs N D l Hle.
unfold rbn_L3_run. intros HCX HREC HBUF HL1 HL23 HALL HSRC HSEP HNS HDS HVL G20 G21 G24 G26 G27.
exact (rbn3_run fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs N D l
  HCX HREC HBUF HL1 HL23 HALL HSRC HSEP HNS HDS HVL G20 G21 G24 G26 G27).
Qed.
Theorem rbn_l3_ovf : rbn_L3_ovf B.
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs N D l Hlt.
unfold rbn_L3_run. intros HCX HREC HBUF HL1 HL23 HALL HSRC HSEP HNS HDS HVL G20 G21 G24 G26 G27.
exfalso. pose proof (bn_tk_len l false) as HB. unfold bn_TK in Hlt. lia.
Qed.
End h.
End f.
End d.
