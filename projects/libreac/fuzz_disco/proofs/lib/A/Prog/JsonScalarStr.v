(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YC1f.v, with its module paths and module names changed; 593 of its 625 lines of code are new or changed and 459 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1h YC4b YC85 YC88 DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import JsonScalarBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import ConstsViewDef StrlenDef MemchrDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require Import McConsts.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Set Default Proof Using "All".
Definition rs_hold (A : Prop) : Prop := A.
Lemma rs_hide : forall A : Prop, A -> rs_hold A. Proof. intros A H. exact H. Qed.
Definition rs_hmod (x y r : Z) : Prop := x mod y = r.
Lemma rs_hide_mod : forall x y r : Z, x mod y = r -> rs_hmod x y r. Proof. intros x y r H. exact H. Qed.
Ltac rs_hide_all := repeat match goal with
  | H : _ \/ _ |- _ => apply rs_hide in H
  | H : _ mod _ = _ |- _ => apply rs_hide_mod in H end.
#[local] Ltac jslim := repeat match goal with
  | H : st_ok_pi _ _ _ _ _ |- _ => clear H
  | H : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => clear H
  | H : sh_ok _ _ _ _ _ |- _ => clear H
  | H : forall _ : world _, _ |- _ => clear H
  | H : forall _ : nat, _ |- _ => clear H
  | H : forall _ : YK11.FPState, _ |- _ => clear H
  end.
#[local] Ltac jlia := jslim; (try YM03.lf_prune0); Zify.zify; xlia zchecker.
#[local] Ltac jlia_full := jslim; Zify.zify; xlia zchecker.
#[local] Ltac jlia_c := first [ apply Nat.ltb_lt; reflexivity | split; [apply Z.leb_le | apply Z.ltb_lt]; reflexivity | jslim; lia ].
#[local] Ltac jconvf Hc :=
  let jU := idtac; lazymatch goal with AGx : forall kk, (kk < 512)%nat -> ew _ kk = ew _ kk |- _ => first [eassumption | rewrite AGx by jlia_c; eassumption] end in
  let jR := idtac; first [jslim; lia | lazymatch goal with Hz : forall t, _ -> 0 <= jbyte _ t < 256 |- _ => apply Hz; jslim; lia end] in
  lazymatch type of Hc with
  | branch_taken BC_EQ (sv_denot ?Ex (SOff ?nn 0)) (sv_denot _ (SLit 0)) = ?bb =>
    lazymatch goal with
    | MW : ew Ex nn = ?w, HRm : (?w = w64 0 <-> ?P) |- _ =>
      lazymatch bb with
      | true => let Hm := fresh "Hm" in pose proof (proj1 HRm (proj1 (Lbr_eq0 Ex nn w MW) Hc)) as Hm; destruct Hm
      | false => let Hm := fresh "Hm" in
        assert (Hm : ~ P) by (let X := fresh in intros X; apply (proj2 HRm) in X; apply (proj2 (Lbr_eq0 Ex nn w MW)) in X;
          rewrite X in Hc; discriminate Hc)
      end; clear Hc
    | _ => rewrite (Lbr_eq_lit Ex nn _ 0 ltac:(jU) ltac:(jlia_c)) in Hc
    end
  | branch_taken BC_EQ (sv_denot ?Ex (SOff ?nn 0)) (sv_denot _ (SLit ?z)) = _ =>
    rewrite (Lbr_eq_lit Ex nn _ z ltac:(jU) ltac:(jlia_c)) in Hc
  | branch_taken BC_NE (sv_denot ?Ex (SOff ?nn 0)) (sv_denot _ (SLit ?z)) = _ =>
    rewrite (Lbr_ne_lit Ex nn _ z ltac:(jU) ltac:(jlia_c)) in Hc
  | branch_taken BC_LTU (sv_denot ?Ex (SOff ?nn 0)) (sv_denot _ (SLit ?z)) = _ =>
    rewrite (Lbr_ltu_lit Ex nn _ z ltac:(jU) ltac:(jlia_c)) in Hc
  | branch_taken BC_GEU (sv_denot ?Ex (SOff ?na ?c)) (sv_denot _ (SOff ?nb 0)) = _ =>
    rewrite (Lbr_geu_off Ex na nb _ _ c ltac:(jU) ltac:(jU) ltac:(jlia_c)) in Hc
  | branch_taken BC_LTU (sv_denot ?Ex (SAlu ALU_ADD (SOff ?na 0) (SMd M_MUL (SOff ?nb ?c) (SLit (-1))))) (sv_denot _ (SLit ?z)) = _ =>
    rewrite (Lbr_ltu_sub Ex na nb _ _ c z ltac:(jU) ltac:(jU) ltac:(jlia_c) ltac:(jlia_c)) in Hc
  | branch_taken BC_LTU (sv_denot ?Ex (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff ?na 0) (SLit (-1))) (SLit ?d)) (SOff ?nb 0))) (sv_denot _ (SLit ?z)) = _ =>
    rewrite (Lbr_ltu_sub2 Ex na nb _ _ d z ltac:(jU) ltac:(jU) ltac:(jlia_c) ltac:(jlia_c)) in Hc
  | branch_taken BC_LTU (sv_denot ?Ex (SLit 18446744073709551605)) (sv_denot _ (SOff ?nn (-58))) = _ =>
    rewrite (Lbr_dig Ex nn _ ltac:(jU) ltac:(jR)) in Hc
  | branch_taken BC_LTU (sv_denot ?Ex (SAlu ALU_ADD (SAlu ALU_AND (SOff ?nn 0) (SLit 223)) (SLit (-71)))) (sv_denot _ (SLit 18446744073709551610)) = _ =>
    rewrite (Lbr_hex Ex nn _ ltac:(jU) ltac:(jR) ltac:(assumption)) in Hc
  end;
  try (rewrite ?Bool.negb_true_iff, ?Bool.negb_false_iff in Hc);
  try (rewrite ?Z.eqb_eq, ?Z.eqb_neq, ?Z.ltb_lt, ?Z.ltb_ge in Hc);
  try (let BF := fresh "BF" in rename Hc into BF);
  repeat match goal with
  | H1 : ~ (jesc ?x = false /\ ?x <> 0), H2 : ?x <> 0 |- _ => pose proof (jesc_true x H1 H2); clear H1
  end.
#[local] Ltac jrun_to_tok RUNTO HS HJ SHOK Bspan stop :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
lazymatch paj_tables RUNTO with (?tpi, ?tw) =>
let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
let r := eval vm_compute in (sym_run_toN_pi_tok tpi tw K Bx Bspan SH FUEL stop ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN_pi_tok tpi tw K Bx Bspan SH FUEL stop ss = (st', rs)) by (vm_compute; reflexivity);
let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "jrun_to_tok: no hypothesis  img_env _ _ E" end in
eapply (RUNTO W FUEL stop E K Bx Bspan SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ ltac:(apply Nat.leb_le; reflexivity) HEI HS SHOK
ltac:(vm_compute; reflexivity) Hrun HJ);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
paj_after_run_tok HS HJ SHOK ]
end end
end
| _ => fail "jrun_to_tok: HS must be  st_ok_pi segs val E ss (restrict (w_H W) ms)"
end.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
Definition jsstr_ok (W : world SEGS) (mem : word -> option byte) (a : Z) (s : list Z) : Prop :=
  Forall (fun c => 0 < c < 256) s /\
  garr8 SEGS (mrestrict (w_H W) mem) a (s ++ [0]) /\
  0 < a /\ a + Z.of_nat (length s) + 1 <= 2 ^ 63 /\ Z.of_nat (length s) + 1 < 2 ^ 32 /\
  amem_range a (Z.of_nat (length s) + 1) /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a (Z.of_nat (length s) + 1) /\
  shadow_hull_vis (aview SEGS (w_H W) mem) a (Z.of_nat (length s) + 1) /\
  (forall x, a + Z.of_nat (length s) < x < a + Z.of_nat (length s) - (a + Z.of_nat (length s)) mod 8 + 8 ->
     aview SEGS (w_H W) mem x <> None) /\
  (forall x, a <= x < a + Z.of_nat (length s) + 1 -> in_img SEGS x).
Section h.
Context {B : asyms}.
Hypothesis AMEMCHR : forall fq : YK11.FPState,
  amemchr_realizesM (fx := fq) SEGS B MC_CONSTS_LO MC_CONSTS_HI (@pa_sigma _ disco_listing PI DS___interceptor_trampoline_memchr).
Section J.
Context {fq : YK11.FPState} {STK sp0 : Z} {FP : list (Z * Z)} {ly : alayout} {S : astate} {W0 : world SEGS}
  {mem0 : word -> option byte} {md0 : Model} {own : list (Z * Z)} {lyc : alayout} {Sc : astate} {W : world SEGS}
  {memc : word -> option byte} {k : Z} {regs0 : bvmap 5 word} {b i n v : Z} {BS : list byte} {mdc : Model}.
Context `{JHI : @JH rc SK PI B fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs0 b i n v BS mdc}.
Let LAWS : AR_laws SEGS B := jh_LAWS.
Let HJ0 : ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k := jh_HJ0.
Let Hvimg : off_img v 20 := jh_Hvimg.
Let Hsp16 : spZ regs0 mod 16 = 0 := jh_Hsp16.
Let HspSTK : sp0 - STK <= spZ regs0 - TJSON_SCALAR_STK := jh_HspSTK.
Let Hsp0 : spZ regs0 <= sp0 := jh_Hsp0.
Let Hv0 : 0 < v := jh_Hv0.
Let Hv8 : v mod 8 = 0 := jh_Hv8.
Let Hv63 : v + 20 <= 2 ^ 63 := jh_Hv63.
Let Hvw : spZ regs0 <= v \/ v + 20 <= spZ regs0 - TJSON_SCALAR_STK := jh_Hvw.
Let Hra : YK0s.ret_ok (getr regs0 1) := jh_Hra.
Let RUN := paj_run (fx := fq) B LAWS.
Let RUNTO := paj_run_to (fx := fq) B LAWS.
Let BR := paj_branch (fx := fq) (PI := PI).
Let HLn : Z.of_nat (length BS) = n := jh_HLn.
Let HBS : garr8 SEGS (mrestrict (w_H W) memc) b BZ := jh_HBS.
Let Hb0 : 0 < b := jh_Hb0.
Let Hbam : amem_range b n := jh_Hbam.
Let Hbw : b + n <= spZ regs0 - TJSON_SCALAR_STK \/ spZ regs0 <= b := jh_Hbw.
Let Hvam : amem_range v 20 := jh_Hvam.
Let Hvra : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF v 20 := jh_Hvra.
Let Hvaw : forall a, v <= a < v + 20 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\
  apresent (w_H W) memc a := jh_Hvaw.
Let Hbv : b + n <= v \/ v + 20 <= b := jh_Hbv.
Let Hbra : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF b n := jh_Hbra.
Hypothesis Hs13 : jsstr_ok W memc (VAL (A_OBJ 19)) [34; 92; 47; 98; 102; 110; 114; 116; 117].
Hypothesis Hcv : consts_view SEGS MC_CONSTS_LO MC_CONSTS_HI W memc.
Hypothesis Hgp : getr regs0 3 = w64 (as_gp B).
Hypothesis Htp : getr regs0 4 = w64 (as_tp B).
Definition JS_STR : Z := 0x2f6c.
Definition jal_str : list (sv * sv) :=
  [(SAlu ALU_ADD (SOff 20 0) (SOff 27 0), SOff 45 0); (SAlu ALU_ADD (SOff 20 0) (SOff 8 2), SOff 45 1);
   (SAlu ALU_ADD (SOff 20 0) (SOff 8 0), SOff 45 (-1)); (SAlu ALU_ADD (SOff 20 0) (SOff 8 6), SOff 45 5)].
Lemma jal_str_ok : forall R j la, getr R 20 = w64 b -> getr R 27 = w64 j -> getr R 8 = w64 (j - 1) -> 1 <= j < n ->
  alias_ok (JE R j la) jal_str.
Proof.
intros R j la H20 H27 H8 Hj. pose proof jb_hi as Hbhi.
assert (UP : bv_unsigned (ew (JE R j la) 45) = b + j) by (rewrite jE_P; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew (JE R j la) 20) = b) by (apply (jU_reg R j la 20 20%bv); [lia | reflexivity | exact H20 | lia]).
assert (U27 : bv_unsigned (ew (JE R j la) 27) = j) by (apply (jU_reg R j la 27 27%bv); [lia | reflexivity | exact H27 | lia]).
assert (U8 : bv_unsigned (ew (JE R j la) 8) = j - 1) by (apply (jU_reg R j la 8 8%bv); [lia | reflexivity | exact H8 | lia]).
unfold jal_str. cbn [alias_ok].
split; [apply (jalias_add _ _ _ _ _ _ _ _ _ U20 U27 UP); f_equal; lia|].
split; [apply (jalias_add _ _ _ _ _ _ _ _ _ U20 U8 UP); f_equal; lia|].
split; [apply (jalias_add _ _ _ _ _ _ _ _ _ U20 U8 UP); f_equal; lia|].
split; [apply (jalias_add _ _ _ _ _ _ _ _ _ U20 U8 UP); f_equal; lia|].
exact I.
Qed.
Definition JS_SEND : Z := 0x32fc.
Lemma str_end : forall Q, JEPI_K Q -> forall R M md j, JINV R M md -> getr R 26 = w64 v -> getr R 18 = w64 (b + i) -> getr R 8 = w64 (j - 1) ->
  getr R 23 = w64 i -> 0 <= i -> i < j < n -> jscalar BZ i = Some (j + 1, 1, i + 1, j - i - 1) ->
  SRr SEGS W (mkCfg (mkst R (Z_to_bv 64 (BASE + JS_SEND)) M (seg_rom SEGS)) md) Q.
Proof.
intros Q HQ R M md j HI H26 H18 H8 H23 Hi0 Hij Hjs.
pose proof (jvstate R M md JS_SEND j 26 26%bv [] HI ltac:(lia) ltac:(lia) eq_refl H26 I) as HS.
pose proof (jvshok R M md j 26 26%bv HI ltac:(lia) ltac:(lia) eq_refl H26) as SHOK.
pose proof HI as (HJ & HSL & HK & HPR & H2 & H3 & H4 & H9 & H19 & H20).
pose proof jb_hi as Hbhi. pose proof jsp_hi as Hsph. pose proof jwin_lo as Hwl.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TJSON_SCALAR_STK = 128 + 2 * 4096) by reflexivity.
rs_hide_all.
assert (Hvhi : v + 20 <= 0x7fffffffffff) by (unfold amem_range in Hvam; lia).
assert (UV : bv_unsigned (ew (JE R j 0) 26) = v) by (apply (jU_reg R j 0 26 26%bv); [lia | reflexivity | exact H26 | lia]).
assert (Usp : bv_unsigned (ew (JE R j 0) 2) = spZ regs0 - 128) by (apply (jU_reg R j 0 2 2%bv); [lia | reflexivity | exact H2 | lia]).
assert (UP : bv_unsigned (ew (JE R j 0) 45) = b + j) by (rewrite jE_P; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew (JE R j 0) 18) = b + i) by (apply (jU_reg R j 0 18 18%bv); [lia | reflexivity | exact H18 | lia]).
assert (U8 : bv_unsigned (ew (JE R j 0) 8) = j - 1) by (apply (jU_reg R j 0 8 8%bv); [lia | reflexivity | exact H8 | lia]).
assert (U23 : bv_unsigned (ew (JE R j 0) 23) = i) by (apply (jU_reg R j 0 23 23%bv); [lia | reflexivity | exact H23 | lia]).
assert (E3 : ew (JE R j 0) 3 = getr R 3) by (apply jE_low; [lia | reflexivity]).
assert (E4 : ew (JE R j 0) 4 = getr R 4) by (apply jE_low; [lia | reflexivity]).
set (E := JE R j 0) in *.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
jrun_to_tok RUNTO HS HJ SHOK JBspan JS_EPI.
- cbn [ss_mem].
  apply (awr_ok_cons_gen E (vreg 26) _ STK sp0 FP _ _ lyc own 26%nat v); [reflexivity | exact UV | intros a Ha; apply Hvaw; cbn in Ha; lia |].
  apply (awr_ok_cons_stack_off E jframe _ STK sp0 FP _ _ lyc own 2%nat (spZ regs0 - 128 - sp0)); [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
- assert (HWR : forall a, in_wrange E [vreg 26; jframe; jbytes 0] a ->
    (spZ regs0 - TJSON_SCALAR_STK <= a < spZ regs0) \/ (v <= a < v + 20)).
  { intros a (rg & Hin & Ha). cbn [In] in Hin. destruct Hin as [<-|[<-|[<-|[]]]];
    cbn [vreg jframe jbytes YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?UV, ?Usp, ?UP in Ha; lia. }
  lazymatch type of HS with st_ok_pi _ _ ?En _ _ => set (E2 := En) in HS end.
  assert (AG : forall kk, (kk < 512)%nat -> ew E2 kk = ew E kk)
    by (intros kk Hkk; subst E2; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; reflexivity).
  assert (UV2 : bv_unsigned (ew E2 26) = v) by (rewrite AG by lia; exact UV).
  assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs0 - 128) by (rewrite AG by lia; exact Usp).
  assert (U18' : bv_unsigned (ew E2 18) = b + i) by (rewrite AG by lia; exact U18).
  assert (U8' : bv_unsigned (ew E2 8) = j - 1) by (rewrite AG by lia; exact U8).
  assert (U23' : bv_unsigned (ew E2 23) = i) by (rewrite AG by lia; exact U23).
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10.
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
  pmkst HS.
  apply (HQ (ms_regs ms) (ms_mem ms) _ (j + 1) HJ).
  + rewrite Q2. rewrite ?AG by lia. apply bv_eq. rewrite Usp. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  + rewrite Q3. rewrite ?AG by lia. rewrite E3. exact H3.
  + rewrite Q4. rewrite ?AG by lia. rewrite E4. exact H4.
  + rewrite Q10, U8'. unfold w64. f_equal. lia.
  + lia.
  + apply (jslots_of E2 _ ms 1 _ HS eq_refl).
    * intros c Hc. cbn [jframe_chunks In] in Hc |- *. clear - Hc. tauto.
    * exact Usp2.
    * intros t Ht. rewrite AG by lia. apply jE_X. exact Ht.
  + exact (jpres_of _ _ HG HPR).
  + unfold JRES. change (map bv_unsigned BS) with BZ. rewrite Hjs. split; [reflexivity|].
    split; [|split; [|split]].
    * pose proof (field_of_region E2 _ 26 v _ 0 20 0 20 0 8 (SOff 18 1) (b + (i + 1)) HR0 UV2
        ltac:(cbn [In]; tauto) ltac:(rewrite (jdenot_soff E2 18 (b + i) 1 U18'); f_equal; lia) ltac:(lia) ltac:(cbn; lia)) as Hv.
      rewrite Z.add_0_r in Hv. exact Hv.
    * exact (field_of_region E2 _ 26 v _ 0 20 0 20 8 8 _ (j - i - 1) HR0 UV2
        ltac:(cbn [In]; tauto) ltac:(rewrite (jdenot_sub E2 8 23 (j - 1) i U8' U23') by lia; f_equal; lia) ltac:(lia) ltac:(cbn; lia)).
    * exact (field_of_region E2 _ 26 v _ 0 20 0 20 16 4 (SLit 1) 1 HR0 UV2
        ltac:(cbn [In]; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)).
    * exact (jkeepv_of E _ M (ms_mem ms) HFr HWR HK).
Qed.
Definition STR13 : list Z := [34; 92; 47; 98; 102; 110; 114; 116; 117].
Lemma garr8_aview_at : forall H m a L (t : nat), garr8 SEGS (mrestrict H m) a L -> (t < length L)%nat ->
  aview SEGS H m (a + Z.of_nat t) = Some (nth t L 0).
Proof.
intros H m a L t HG Ht. destruct (HG t Ht) as [Hv Hr]. specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv.
rewrite Z.add_0_r in Hv. unfold aview. rewrite Hv. cbn [option_map]. f_equal.
rewrite le_byte_1_0 by lia. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.
Lemma jmemchr_res : forall (rd : Z -> option Z) x c kk,
  (forall t, (t < 10)%nat -> rd (x + Z.of_nat t) = Some (nth t (STR13 ++ [0]) 0)) ->
  0 <= kk <= 10 -> (forall t, 0 <= t < kk -> exists b', rd (x + t) = Some b' /\ b' <> c) -> (kk < 10 -> rd (x + kk) = Some c) ->
  (kk = 10 <-> (jesc c = false /\ c <> 0)).
Proof.
intros rd x c kk Hrd Hk Hbef Hat. split.
- intros ->.
  assert (Hne : forall t, (t < 10)%nat -> nth t (STR13 ++ [0]) 0 <> c).
  { intros t Ht Heq. destruct (Hbef (Z.of_nat t) ltac:(lia)) as (b' & Hb & Hbc). rewrite Hrd in Hb by exact Ht.
    injection Hb as <-. contradiction. }
  pose proof (Hne 0%nat ltac:(lia)) as N0. pose proof (Hne 1%nat ltac:(lia)) as N1. pose proof (Hne 2%nat ltac:(lia)) as N2.
  pose proof (Hne 3%nat ltac:(lia)) as N3. pose proof (Hne 4%nat ltac:(lia)) as N4. pose proof (Hne 5%nat ltac:(lia)) as N5.
  pose proof (Hne 6%nat ltac:(lia)) as N6. pose proof (Hne 7%nat ltac:(lia)) as N7. pose proof (Hne 8%nat ltac:(lia)) as N8.
  pose proof (Hne 9%nat ltac:(lia)) as N9. cbn in N0, N1, N2, N3, N4, N5, N6, N7, N8, N9.
  split; [|lia]. unfold jesc. cbn [existsb].
  repeat rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity.
- intros [Hj Hc0]. destruct (Z.eq_dec kk 10) as [->|Hk10]; [reflexivity|]. exfalso.
  pose proof (Hat ltac:(lia)) as Hk'. replace kk with (Z.of_nat (Z.to_nat kk)) in Hk' by lia.
  rewrite Hrd in Hk' by lia. injection Hk' as Hk'.
  assert (Ht : (Z.to_nat kk < 10)%nat) by lia. revert Hk' Ht. generalize (Z.to_nat kk). intros t Hk' Ht.
  do 10 (destruct t as [|t]; [cbn in Hk'; subst c; first [discriminate Hj | lia] |]). lia.
Qed.
Lemma jimg_low : forall a, in_img SEGS a -> 0 <= a < 2 ^ 64 /\ ~ (spZ regs0 - TJSON_SCALAR_STK <= a < spZ regs0).
Proof.
intros a Ha. pose proof (pa_segs_low a Ha). pose proof jwin_lo as Hwl. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). lia.
Qed.
Lemma js_memchr : forall regsT memT mdT c raw,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k -> JKEEP memT ->
  getr regsT 10 = w64 (VAL (A_OBJ 19)) -> getr regsT 11 = w64 c -> getr regsT 12 = w64 10 -> 0 <= c < 256 ->
  spZ regsT = spZ regs0 - 128 -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (@pa_sigma _ disco_listing PI DS___interceptor_trampoline_memchr)) memT (seg_rom SEGS)) mdT)
  (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
     c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
     ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
     aregs_preserved regsT regs2 /\
     (getr regs2 10 = w64 0 <-> (jesc c = false /\ c <> 0)) /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - ESTACK <= a < spZ regsT) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
     (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros regsT memT mdT c raw HJ HK Ha0 Ha1 Ha2 Hc Hsp Hgp' Htp' Hra' Hraw.
pose proof pa_segs_low as Hsegs. pose proof jsp_hi as Hsph. pose proof jwin_lo as Hwl.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TJSON_SCALAR_STK = 128 + 2 * 4096) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hs13 as Hs13'.
destruct Hs13' as (_ & Hg13 & Hx0 & Hx63 & _ & Ham & Hxra & Hxhull & _ & Hximg).
cbn [length STR13 Z.of_nat] in Hx63, Ham, Hxra, Hxhull, Hximg.
set (x := VAL (A_OBJ 19)) in *.
assert (Hxi : forall a, x <= a < x + 10 -> 0 <= a < 2 ^ 64 /\ ~ (spZ regs0 - TJSON_SCALAR_STK <= a < spZ regs0))
  by (intros a Ha; apply jimg_low; apply Hximg; lia).
assert (Hxlo : x + 10 <= kLowMemEnd) by (pose proof (Hsegs (x + 9) (Hximg (x + 9) ltac:(lia))); lia).
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdT).
{ apply (ecall_pre_at SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k regsT (spZ regs0 - 128 - sp0) HJ);
  [lia | pose proof Hsp16 as Hs16; clear - Hal16 Hs16; Z.div_mod_to_equations; lia | lia | lia | rewrite Hra'; exact Hraw | exact Hgp' | exact Htp']. }
assert (Hrd : forall t, (t < 10)%nat -> aview SEGS (w_H W) memT (x + Z.of_nat t) = Some (nth t (STR13 ++ [0]) 0)).
{ intros t Ht. destruct (Hxi (x + Z.of_nat t) ltac:(lia)) as [Ha1' Ha2']. rewrite (HK _ Ha1' Ha2').
  apply garr8_aview_at; [exact Hg13 | cbn; lia]. }
eapply SRr_mono.
{ apply (AMEMCHR fq lyc Sc W regsT memT mdT x c 10 HPRE Ha0 Ha1 Ha2 ltac:(lia) ltac:(lia) Hx0 ltac:(lia)).
  - intros a Ha. split; [|rewrite Hsp; lia].
    replace a with (x + Z.of_nat (Z.to_nat (a - x))) by lia. rewrite Hrd by lia. discriminate.
  - exact Ham.
  - apply (range_addressable_kept_win (aview SEGS (w_H W) memc) (aview SEGS (w_H W) memT) (spZ regs0 - TJSON_SCALAR_STK) (spZ regs0));
    [intros s Hs Hn; apply HK; assumption | lia | lia | lia | exact Hxra].
  - intros _. apply (shadow_hull_vis_kept_win (aview SEGS (w_H W) memc) (aview SEGS (w_H W) memT) (spZ regs0 - TJSON_SCALAR_STK) (spZ regs0));
    [intros s Hs Hn; apply HK; assumption | lia | lia | lia | lia | exact Hxhull].
  - apply (consts_view_keep SEGS _ _ W memc memT Hcv). intros a Ha. unfold MC_CONSTS_LO, MC_CONSTS_HI in Ha.
    pose proof jwin_lo as Hwl0. pose proof alloc_ceiling_val as Hcl. apply HK; lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & (kk & Hfb & Hres) & Hfr & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra'; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write SEGS B LAWS Hsegs STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k mem2 md2
    (fun a => spZ regsT - ESTACK <= a < spZ regsT) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha). exact Hna.
  - exact Hpres2.
  - exact Hsame.
  - intros a Ha; left; left; lia.
  - exact HAR2.
  - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
split; [exact HP|].
split; [|split; [exact Hfr | exact Hpres2]].
destruct Hfb as (Hk10 & Hbef & Hat).
rewrite <- (jmemchr_res (aview SEGS (w_H W) memT) x c kk Hrd Hk10 Hbef Hat).
rewrite Hres. destruct (Z.ltb_spec kk 10) as [Hlt|Hge].
- split; [|lia]. intros Heq. exfalso. apply (f_equal bv_unsigned) in Heq. unfold w64 in Heq.
  rewrite !unsigned_lit_small in Heq by lia. lia.
- split; [intros _; lia | intros _; reflexivity].
Qed.
Lemma jstr_quote : forall L i0 j f, j < jlen L -> jbyte L j = 34 -> jstr L i0 j (Datatypes.S f) = Some (j + 1, 1, i0 + 1, j - i0 - 1).
Proof. intros L i0 j f H1 H2. cbn [jstr]. rewrite (proj2 (Z.leb_gt _ _) H1), H2. reflexivity. Qed.
Lemma jstr_ctl : forall L i0 j f, j < jlen L -> jbyte L j <> 34 -> jbyte L j < 32 -> jstr L i0 j (Datatypes.S f) = None.
Proof.
intros L i0 j f H1 H2 H3. cbn [jstr]. rewrite (proj2 (Z.leb_gt _ _) H1), (proj2 (Z.eqb_neq _ _) H2), (proj2 (Z.ltb_lt _ _) H3).
reflexivity.
Qed.
Lemma jstr_plain : forall L i0 j f, j < jlen L -> jbyte L j <> 34 -> 32 <= jbyte L j -> jbyte L j <> 92 ->
  jstr L i0 j (Datatypes.S f) = jstr L i0 (j + 1) f.
Proof.
intros L i0 j f H1 H2 H3 H4. cbn [jstr]. rewrite (proj2 (Z.leb_gt _ _) H1), (proj2 (Z.eqb_neq _ _) H2), (proj2 (Z.ltb_ge _ _) H3),
  (proj2 (Z.eqb_neq _ _) H4). reflexivity.
Qed.
Lemma jstr_bs : forall L i0 j f, j < jlen L -> jbyte L j = 92 ->
  jstr L i0 j (Datatypes.S f) =
    if jlen L <=? j + 1 then None
    else if negb (jesc (jbyte L (j + 1))) then None
    else if jbyte L (j + 1) =? 117 then
      if (jlen L - (j + 1) <=? 4) ||
         negb (jhexd (jbyte L (j + 2)) && jhexd (jbyte L (j + 3)) && jhexd (jbyte L (j + 4)) && jhexd (jbyte L (j + 5)))
      then None else jstr L i0 (j + 6) f
    else jstr L i0 (j + 2) f.
Proof. intros L i0 j f H1 H2. cbn [jstr]. rewrite (proj2 (Z.leb_gt _ _) H1), H2. reflexivity. Qed.
Lemma jstr_end : forall L i0 j f, jlen L <= j -> jstr L i0 j f = None.
Proof. intros L i0 j [|f] H; [reflexivity|]. cbn [jstr]. rewrite (proj2 (Z.leb_le _ _) H). reflexivity. Qed.
Lemma jhex_of_dig : forall c, jdigit c = true -> jhexd c = true.
Proof. intros c H. unfold jhexd. rewrite H. reflexivity. Qed.
Ltac jdecide :=
  rewrite ?jlen_BZ;
  repeat first
  [ match goal with H : jesc ?x = _ |- context [jesc ?x] => rewrite H end
  | match goal with H : jhexd ?x = _ |- context [jhexd ?x] => rewrite H end
  | match goal with H : jdigit ?x = true |- context [jhexd ?x] => rewrite (jhex_of_dig x H) end
  | match goal with H : jbyte BZ ?x = 0 |- context [jesc (jbyte BZ ?x)] => rewrite H end
  | progress cbn [negb andb orb]
  | rewrite (proj2 (Z.leb_le _ _)) by jlia
  | rewrite (proj2 (Z.leb_gt _ _)) by jlia
  | rewrite (proj2 (Z.eqb_eq _ _)) by jlia
  | rewrite (proj2 (Z.eqb_neq _ _)) by jlia ].
Ltac jstr_dec :=
  first
  [ lazymatch goal with
    | _ : jbyte BZ ?j = 34 |- context [jstr BZ _ ?j (Datatypes.S _)] => rewrite jstr_quote by (rewrite ?jlen_BZ; jlia)
    | _ : jbyte BZ ?j < 32 |- context [jstr BZ _ ?j (Datatypes.S _)] => rewrite jstr_ctl by (rewrite ?jlen_BZ; jlia)
    | _ : jbyte BZ ?j = 92 |- context [jstr BZ _ ?j (Datatypes.S _)] => rewrite jstr_bs by (rewrite ?jlen_BZ; jlia); jdecide
    | _ : jbyte BZ ?j <> 92 |- context [jstr BZ _ ?j (Datatypes.S _)] => rewrite jstr_plain by (rewrite ?jlen_BZ; jlia)
    end
  | rewrite jstr_quote by (rewrite ?jlen_BZ; jlia)
  | rewrite jstr_ctl by (rewrite ?jlen_BZ; jlia)
  | rewrite jstr_plain by (rewrite ?jlen_BZ; jlia)
  | rewrite jstr_bs by (rewrite ?jlen_BZ; jlia); jdecide ];
  try (rewrite jstr_end by (rewrite ?jlen_BZ; jlia)).
Definition JS_SBR1 : Z := 0x2f84.
Definition JS_SBR2 : Z := 0x30c4.
Lemma str_loop : forall Q, JEPI_K Q -> forall (m : nat) R M md j f,
  Z.of_nat m = n - j -> JINV R M md ->
  getr R 27 = w64 j -> getr R 8 = w64 (j - 1) -> getr R 18 = w64 (b + i) -> getr R 23 = w64 i ->
  getr R 26 = w64 v -> getr R 24 = w64 34 -> getr R 25 = w64 32 -> getr R 13 = w64 92 ->
  getr R 21 = w64 (VAL (A_OBJ 19)) ->
  0 <= i -> i < j < n -> n - j < Z.of_nat f -> jscalar BZ i = jstr BZ i j f ->
  SRr SEGS W (mkCfg (mkst R (Z_to_bv 64 (BASE + JS_STR)) M (seg_rom SEGS)) md) Q.
Proof.
intros Q HQ m. induction m as [m IH] using lt_wf_ind.
intros R M md j f Hm HI H27 H8 H18 H23 H26 H24 H25 H13 H21 Hi0 Hij Hf HJS.
destruct f as [|f]; [cbn in Hf; lia|].
pose proof HI as (HJ & HSL & MEQ & PRS & H2 & H3 & H4 & H9 & H19 & H20).
pose proof jb_hi as Hbhi. pose proof jsp_hi as Hsph. pose proof jwin_lo as Hwl.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TJSON_SCALAR_STK = 128 + 2 * 4096) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HnZ : forall t, 0 <= t < n -> 0 <= jbyte BZ t < 256) by (intros t Ht; exact (proj2 (jbyte_mem M t MEQ Ht))).
rs_hide_all.
assert (Hla : n - j = 1 \/ (2 <= n - j <= 5) \/ 6 <= n - j) by lia.
let rec go T :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ecur ?ss0 _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  jrun_to_tok RUNTO HS HJ SHOK JBspan T;
  [ lazymatch goal with
    | |- range_addressable _ _ (U _ (SOff 45 ?t)) 1 =>
      cbn [ms_mem mkst]; apply (jobl _ _ j t MEQ); [rewrite AG by jlia_c; exact U9 | rewrite AG by jlia_c; exact U45 | lia | lia | lia]
    | |- awr_ok _ _ _ _ _ _ _ _ _ => apply jawr_std; [vm_compute; reflexivity | rewrite AG by jlia_c; exact U2]
    end ..
  | jpost Ecur ]
  end
with jpost Ecur :=
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdl _ |- _ =>
    lazymatch mdl with
    | with_vm_backing _ _ _ => let mdv := fresh "mdv" in set (mdv := mdl) in *; clearbody mdv
    | _ => idtac
    end
  end;
  lazymatch goal with HFr : frame_of ?Eh ?rs (mrestrict _ ?m1) (mrestrict _ ?m2), MEQ : JKEEP ?m1 |- _ =>
    let MEQ2 := fresh "MEQ" in
    pose proof (jkeep_run Eh rs m1 m2 ltac:(vm_compute; reflexivity) ltac:(rewrite AG by jlia_c; exact U2) HFr MEQ) as MEQ2;
    clear MEQ; rename MEQ2 into MEQ
  end;
  lazymatch goal with HG : mem_grows (mrestrict _ ?m1) (mrestrict _ ?m2), PRS : JPRES ?m1 |- _ =>
    let PRS2 := fresh "PRS" in pose proof (jpres_of m1 m2 HG PRS) as PRS2; clear PRS; rename PRS2 into PRS
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?En _ _ |- _ => jrebase En Ecur
  | HS : st_ok _ ?En _ _ |- _ => jrebase En Ecur
  end;
  lazymatch goal with
  | HS : st_ok _ _ (setpc _ _) _ |- _ => jcall; go JS_EPI
  | HS : st_ok_pi _ _ _ ?ss _ |- _ =>
    let pc := eval vm_compute in (ss_pc ss) in
    lazymatch pc with
    | 12740 => jexit_epi
    | 12140 => jexit_loop
    | 13052 => jexit_send
    | 12164 => psrr_branch_tok RUN BR HS SHOK JBspan;
               [jconvf Hc; first [exfalso; jlia_full | go JS_SEND] | jconvf Hc; first [exfalso; jlia_full | go JS_EPI]]
    | 12484 => psrr_branch_tok RUN BR HS SHOK JBspan;
               [jconvf Hc; first [exfalso; jlia_full | go JS_EPI] | jconvf Hc; first [exfalso; jlia_full | go JS_STR]]
    | _ => psrr_branch_tok RUN BR HS SHOK JBspan;
               [jconvf Hc; first [exfalso; jlia_full | go JS_EPI] | jconvf Hc; first [exfalso; jlia_full | go JS_EPI]]
    end
  end
with jrebase En Ecur :=
  tryif constr_eq En Ecur then idtac else
  (let E2 := fresh "Ec" in set (E2 := En) in *;
   let AG2 := fresh "AG" in
   assert (AG2 : forall kk, (kk < 512)%nat -> ew E2 kk = ew E0 kk)
     by (intros kk Hkk; subst E2; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; apply AG; exact Hkk);
   clear AG; rename AG2 into AG)
with jcall :=
  lazymatch goal with HS : st_ok _ ?Ec ?ssc (restrict (w_H W) ?msX) |- _ =>
  let K := run_K_hi HS in
  let K4 := eval vm_compute in (K + 4)%nat in
  let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Ra2 := fresh "Ra2" in let Rra := fresh "Rra" in
  let Qsp := fresh "Qsp" in let Qgp := fresh "Qgp" in let Qtp := fresh "Qtp" in
  prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (12%bv : bv 5) Ra2; prreg HS (1%bv : bv 5) Rra;
  prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
  rewrite ?AG in Ra0, Ra1, Qsp, Qgp, Qtp by jlia_c;
  let HspU := fresh "HspU" in
  assert (HspU : spZ (ms_regs msX) = spZ regs0 - 128) by (unfold spZ at 1; rewrite Qsp; exact U2);
  pmkst HS;
  let raw := lazymatch type of Rra with _ = ?r => r end in
  eapply SRr_bind;
  [ apply (js_memchr (ms_regs msX) (ms_mem msX) _ (jbyte BZ (j + 1)) raw HJ MEQ);
    [ rewrite Ra0, EF21; exact H21
    | rewrite Ra1, EC1; reflexivity
    | rewrite Ra2; reflexivity
    | apply HnZ; lia
    | exact HspU
    | rewrite Qgp, EF3, H3; exact Hgp
    | rewrite Qtp, EF4, H4; exact Htp
    | exact Rra
    | apply ret_ok_codeptr_v; [lia | reflexivity] ]
  | cbv beta;
    let W2 := fresh "W2" in let c2 := fresh "c2" in let regs2 := fresh "regs2" in let mem2 := fresh "mem2" in let md2 := fresh "md2" in
    let HJ2 := fresh "HJ2" in let HP2 := fresh "HP2" in let HR := fresh "HR" in let Hfr2 := fresh "Hfr2" in
    let Hpres2 := fresh "Hpres2" in let HPP := fresh "HPP" in
    intros W2 c2 _ HPP; destruct HPP as (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HR & Hfr2 & Hpres2);
    rewrite HspU in Hfr2;
    let HS2 := fresh "HS" in
    jafter_call_keep_hi HS K regs2 (mrestrict (w_H W) mem2) HP2 [0; 1]%nat HS2;
    match type of HS2 with ?tt -> _ => let HRK := fresh in assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end;
    [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
      (eapply jkept_region; [rewrite AG by jlia_c; eassumption | intros; unfold rs_hold in Hbw; lia | exact Hfr2 | exact Hpres2])
    | rewrite <- restrict_mkst_fx in HS2;
      lazymatch type of HS2 with st_ok_pi _ _ ?En _ _ =>
        let E2 := fresh "Ec" in set (E2 := En) in HS2;
        let HEI2 := fresh "HEI" in let AG2 := fresh "AG" in let MW := fresh "MW" in
        let MEQ2 := fresh "MEQ" in let PRS2 := fresh "PRS" in let SHOK2 := fresh "SHOK" in
        assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply img_env_havoc_hi; [assumption | cbv; lia]);
        assert (AG2 : forall kk, (kk < 512)%nat -> ew E2 kk = ew E0 kk)
          by (intros kk Hkk; subst E2; rewrite ew_havoc_old by lia; apply AG; exact Hkk);
        assert (MW : ew E2 K4 = getr regs2 10)
          by (subst E2; change K4 with (K + 4)%nat; rewrite (ew_havoc_new _ K _ 4 (Z_to_bv 64 0)) by (cbn; lia); reflexivity);
        pose proof (jkeep_call (ms_mem msX) mem2 MEQ Hfr2) as MEQ2;
        assert (PRS2 : JPRES mem2) by (intros a Ha; apply Hpres2; apply PRS; exact Ha);
        pose proof (Forall_nil (shent_ok SEGS (SOff 9 0) E2 (mrestrict (w_H W) mem2)) : sh_ok SEGS (SOff 9 0) [] E2 (mrestrict (w_H W) mem2)) as SHOK2;
        clearbody E2;
        clear HS HJ MEQ PRS SHOK AG Ra0 Ra1 Ra2 Rra Qsp Qgp Qtp HspU HP2 Hfr2 Hpres2;
        repeat match goal with H : img_env _ _ ?Ex |- _ => lazymatch Ex with E2 => fail | _ => clear H end end;
        rename HS2 into HS; rename HJ2 into HJ; rename MEQ2 into MEQ; rename PRS2 into PRS; rename SHOK2 into SHOK;
        rename AG2 into AG
      end ] ]
  end
with jrg HS :=
  lazymatch goal with |- getr _ ?r = _ =>
    let Q := fresh "Q" in prreg HS r Q; rewrite Q; clear Q; rewrite ?AG by jlia_c;
    first [ reflexivity
          | rewrite ?EF2, ?EF3, ?EF4, ?EF9, ?EF18, ?EF19, ?EF20, ?EF21, ?EF23, ?EF26; assumption
          | rewrite ?U27, ?U8; unfold w64; f_equal; lia
          | apply bv_eq; rewrite ?U2, ?U8, ?U9, ?U19, ?U20, ?U27, ?U45; unfold w64; rewrite unsigned_lit_small by lia; lia
          ]
  end
with jexit_epi :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ec _ (restrict _ ?msx) |- _ =>
  pmkst HS;
  apply (HQ (ms_regs msx) (ms_mem msx) _ 0 HJ);
  [ jrg HS | jrg HS | jrg HS | jrg HS | lia
  | apply (jslots_of Ec _ msx 0 _ HS eq_refl);
    [ let c := fresh in let Hc0 := fresh in intros c Hc0; cbn [jframe_chunks In] in Hc0 |- *; clear - Hc0; tauto
    | rewrite AG by jlia_c; exact U2
    | let t := fresh in let Ht := fresh in intros t Ht; rewrite AG by jlia_c; apply jE_X; exact Ht ]
  | exact PRS
  | unfold JRES; change (map bv_unsigned BS) with BZ; rewrite HJS; jstr_dec; split; [reflexivity | exact MEQ] ]
  end
with jexit_loop :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ec ?ss (restrict _ ?msx) |- _ =>
  let e27 := eval vm_compute in (sr_get (ss_regs ss) (27%bv : bv 5)) in
  let j' := lazymatch e27 with SOff 27%nat ?c => constr:(j + c) | SOff 8%nat ?c => constr:(j - 1 + c) end in
  pmkst HS;
  apply (IH (Z.to_nat (n - j')) ltac:(lia) (ms_regs msx) (ms_mem msx) _ j' f);
  [ lia
  | split; [exact HJ|]; split;
    [ apply (jslots_of Ec _ msx 0 _ HS eq_refl);
      [ let c := fresh in let Hc0 := fresh in intros c Hc0; cbn [jframe_chunks In] in Hc0 |- *; clear - Hc0; tauto
      | rewrite AG by jlia_c; exact U2
      | let t := fresh in let Ht := fresh in intros t Ht; rewrite AG by jlia_c; apply jE_X; exact Ht ]
    | split; [exact MEQ|]; split; [exact PRS|]; repeat split; jrg HS ]
  | jrg HS | jrg HS | jrg HS | jrg HS | jrg HS | jrg HS | jrg HS | jrg HS | jrg HS
  | lia | lia | lia
  | rewrite HJS; jstr_dec; f_equal; lia ]
  end
with jexit_send :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ec ?ss (restrict _ ?msx) |- _ =>
  pmkst HS;
  apply (str_end Q HQ (ms_regs msx) (ms_mem msx) _ j);
  [ split; [exact HJ|]; split;
    [ apply (jslots_of Ec _ msx 0 _ HS eq_refl);
      [ let c := fresh in let Hc0 := fresh in intros c Hc0; cbn [jframe_chunks In] in Hc0 |- *; clear - Hc0; tauto
      | rewrite AG by jlia_c; exact U2
      | let t := fresh in let Ht := fresh in intros t Ht; rewrite AG by jlia_c; apply jE_X; exact Ht ]
    | split; [exact MEQ|]; split; [exact PRS|]; repeat split; jrg HS ]
  | jrg HS | jrg HS | jrg HS | jrg HS | lia | lia
  | rewrite HJS; apply jstr_quote; [rewrite jlen_BZ; lia | lia] ]
  end in
let sbody la :=
  pose proof (jstate R M md JS_STR j la jal_str HI ltac:(lia) ltac:(lia) ltac:(lia) (jal_str_ok R j la H20 H27 H8 ltac:(lia))) as HS;
  jpin HS 24 34 H24; jpin HS 25 32 H25; jpin HS 13 92 H13;
  assert (U2 : bv_unsigned (ew (JE R j la) 2) = spZ regs0 - 128) by (apply (jU_reg R j la 2 2%bv); [lia | reflexivity | exact H2 | lia]);
  assert (U9 : bv_unsigned (ew (JE R j la) 9) = SHADOW_OFF) by (apply (jU_reg R j la 9 9%bv); [lia | reflexivity | exact H9 | unfold SHADOW_OFF; lia]);
  assert (U19 : bv_unsigned (ew (JE R j la) 19) = n) by (apply (jU_reg R j la 19 19%bv); [lia | reflexivity | exact H19 | lia]);
  assert (U20 : bv_unsigned (ew (JE R j la) 20) = b) by (apply (jU_reg R j la 20 20%bv); [lia | reflexivity | exact H20 | lia]);
  assert (U27 : bv_unsigned (ew (JE R j la) 27) = j) by (apply (jU_reg R j la 27 27%bv); [lia | reflexivity | exact H27 | lia]);
  assert (U8 : bv_unsigned (ew (JE R j la) 8) = j - 1) by (apply (jU_reg R j la 8 8%bv); [lia | reflexivity | exact H8 | lia]);
  assert (U45 : bv_unsigned (ew (JE R j la) 45) = b + j) by (rewrite jE_P; apply unsigned_lit_small; lia);
  assert (EF2 : ew (JE R j la) 2 = getr R 2) by (apply jE_low; [lia | reflexivity]);
  assert (EF3 : ew (JE R j la) 3 = getr R 3) by (apply jE_low; [lia | reflexivity]);
  assert (EF4 : ew (JE R j la) 4 = getr R 4) by (apply jE_low; [lia | reflexivity]);
  assert (EF9 : ew (JE R j la) 9 = getr R 9) by (apply jE_low; [lia | reflexivity]);
  assert (EF18 : ew (JE R j la) 18 = getr R 18) by (apply jE_low; [lia | reflexivity]);
  assert (EF19 : ew (JE R j la) 19 = getr R 19) by (apply jE_low; [lia | reflexivity]);
  assert (EF20 : ew (JE R j la) 20 = getr R 20) by (apply jE_low; [lia | reflexivity]);
  assert (EF21 : ew (JE R j la) 21 = getr R 21) by (apply jE_low; [lia | reflexivity]);
  assert (EF23 : ew (JE R j la) 23 = getr R 23) by (apply jE_low; [lia | reflexivity]);
  assert (EF26 : ew (JE R j la) 26 = getr R 26) by (apply jE_low; [lia | reflexivity]);
  pose proof (jE_C R j la 0 ltac:(lia) ltac:(lia)) as EC0; cbn [Nat.add Z.of_nat] in EC0; rewrite ?Z.add_0_r in EC0;
  assert (UC0 : bv_unsigned (ew (JE R j la) 46) = jbyte BZ j) by (rewrite EC0; apply unsigned_lit_small; pose proof (HnZ j ltac:(lia)); lia);
  try (pose proof (jE_C R j la 1 ltac:(lia) ltac:(lia)) as EC1; cbn [Nat.add Z.of_nat] in EC1;
       assert (UC1 : bv_unsigned (ew (JE R j la) 47) = jbyte BZ (j + 1)) by (rewrite EC1; apply unsigned_lit_small; pose proof (HnZ (j + 1) ltac:(lia)); lia));
  try (pose proof (jE_C R j la 2 ltac:(lia) ltac:(lia)) as EC2; cbn [Nat.add Z.of_nat] in EC2; pose proof (HnZ (j + 2) ltac:(lia)) as HZ2;
       assert (UC2 : bv_unsigned (ew (JE R j la) 48) = jbyte BZ (j + 2)) by (rewrite EC2; apply unsigned_lit_small; lia));
  try (pose proof (jE_C R j la 3 ltac:(lia) ltac:(lia)) as EC3; cbn [Nat.add Z.of_nat] in EC3; pose proof (HnZ (j + 3) ltac:(lia)) as HZ3;
       assert (UC3 : bv_unsigned (ew (JE R j la) 49) = jbyte BZ (j + 3)) by (rewrite EC3; apply unsigned_lit_small; lia));
  try (pose proof (jE_C R j la 4 ltac:(lia) ltac:(lia)) as EC4; cbn [Nat.add Z.of_nat] in EC4; pose proof (HnZ (j + 4) ltac:(lia)) as HZ4;
       assert (UC4 : bv_unsigned (ew (JE R j la) 50) = jbyte BZ (j + 4)) by (rewrite EC4; apply unsigned_lit_small; lia));
  try (pose proof (jE_C R j la 5 ltac:(lia) ltac:(lia)) as EC5; cbn [Nat.add Z.of_nat] in EC5; pose proof (HnZ (j + 5) ltac:(lia)) as HZ5;
       assert (UC5 : bv_unsigned (ew (JE R j la) 51) = jbyte BZ (j + 5)) by (rewrite EC5; apply unsigned_lit_small; lia));
  set (E0 := JE R j la) in *;
  assert (HEI : img_env VAL A_LIM E0) by apply Eimg_env;
  assert (SHOK : sh_ok SEGS (SOff 9 0) [] E0 (mrestrict (w_H W) (ms_mem (mkst R (Z_to_bv 64 (BASE + JS_STR)) M (seg_rom SEGS))))) by apply Forall_nil;
  set (Ec0 := E0) in HS, SHOK, HEI;
  assert (AG : forall kk, (kk < 512)%nat -> ew Ec0 kk = ew E0 kk) by (intros; reflexivity);
  clearbody Ec0;
  change (JKEEP M) with (JKEEP (ms_mem (mkst R (Z_to_bv 64 (BASE + JS_STR)) M (seg_rom SEGS)))) in MEQ;
  change (JPRES M) with (JPRES (ms_mem (mkst R (Z_to_bv 64 (BASE + JS_STR)) M (seg_rom SEGS)))) in PRS;
  go JS_EPI in
destruct Hla as [Hla|[Hla|Hla]]; [sbody 1%nat | sbody 2%nat | sbody 6%nat].
Qed.
End J.
End h.
End f.
End d.
