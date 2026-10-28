(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg FPSteps
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u PmCurDefs_u PmCurSpecs_u PmFloatCSpecs_u PmLibSanity_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop Require Import TopKit_u TopKit2_u TopSpecs_u TopSpecs2_u ReadKit_u ChunkKit_u GetStrStretch_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module GTS.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Definition box (X : Prop) : Prop := X.
Lemma ra_ok_lit : forall z, (0 <=? z) && (z <? 2 ^ 47) && (z mod 2 =? 0) = true -> L5.ra_ok z.
Proof. intros z X. apply andb_prop in X as [X Y3]. apply andb_prop in X as [Y1 Y2]. apply Z.leb_le in Y1. apply Z.ltb_lt in Y2. apply Z.eqb_eq in Y3. split; [lia | exact Y3]. Qed.

Lemma rdn_u8 : forall (M : mem) a (bs : list byte) (i : nat), 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 -> rdn RSEGS M (Z_to_bv 64 a) (length bs) = Some bs -> (i < length bs)%nat ->
  L5.u8_at RSEGS M (a + Z.of_nat i) (bv_unsigned (nth i bs (Z_to_bv 8 0))).
Proof.
  intros M a bs. revert a. induction bs as [|b bs IH]; intros a i Ha Hn Hr Hi; [cbn in Hi; lia|].
  cbn [length rdn] in Hr. destruct (match M (Z_to_bv 64 a) with Some b0 => Some b0 | None => seg_rom RSEGS (Z_to_bv 64 a) end) as [b0|] eqn:E0; [|discriminate].
  destruct (rdn RSEGS M (Z_to_bv 64 a + 1)%bv (length bs)) as [rest|] eqn:ER; [|discriminate]. injection Hr as <- <-.
  destruct i as [|i].
  - unfold L5.u8_at. rewrite Z.add_0_r. cbn [rdn]. rewrite E0. cbn. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite L5C.add1_lit in ER. cbn [length] in Hn. replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. cbn [nth].
    apply IH; [lia | lia | exact ER | cbn in Hi; lia].
Qed.
Lemma u64_0_u8 : forall (M : mem) a (i : nat), 0 <= a -> a + 8 <= 2 ^ 64 -> (i < 8)%nat -> L5.u64_at RSEGS M a 0 -> L5.u8_at RSEGS M (a + Z.of_nat i) 0.
Proof.
  intros M a i Ha Hn Hi H. unfold L5.u64_at in H. set (bs := word_to_le_bytes 8 (Z_to_bv 64 0)) in *.
  pose proof (rdn_u8 M a bs i Ha ltac:(cbn; lia) H ltac:(cbn; lia)) as B.
  assert (E : bv_unsigned (nth i bs (Z_to_bv 8 0)) = 0) by (do 8 (destruct i as [|i]; [reflexivity|]); lia). rewrite E in B. exact B.
Qed.
Lemma sso_empty_of_zero : forall (M : mem) o, 0 <= o -> o + 8 <= 2 ^ 64 -> L5.u64_at RSEGS M o 0 -> L5.lstr_short RSEGS M o [].
Proof.
  intros M o Ho Hn H. unfold L5.lstr_short. cbn [length]. split; [lia|]. pose proof (u64_0_u8 M o 0%nat Ho Hn ltac:(lia) H) as B0. pose proof (u64_0_u8 M o 1%nat Ho Hn ltac:(lia) H) as B1.
  rewrite Z.add_0_r in B0. split; [exact B0|]. split; [intros i Hi; cbn in Hi; lia|]. replace (o + 1 + Z.of_nat 0) with (o + Z.of_nat 1) by lia. exact B1.
Qed.
Lemma bytes_of_defined : forall (M : mem) p (k : nat), (forall i, 0 <= i < Z.of_nat k -> M (Z_to_bv 64 (p + i)) <> None) -> exists bs, length bs = k /\ L5.bytes_at RSEGS M p bs.
Proof.
  intros M p k. revert p. induction k as [|k IH]; intros p H.
  - exists []. split; [reflexivity | intros i Hi; cbn in Hi; lia].
  - destruct (IH (p + 1)) as (bs & Hl & Hb); [intros i Hi; replace (p + 1 + i) with (p + (1 + i)) by lia; apply H; lia|].
    pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. destruct (M (Z_to_bv 64 p)) as [x|] eqn:Hx; [|contradiction].
    exists (bv_unsigned x :: bs). split; [cbn; lia|]. intros i Hi. destruct i as [|i].
    + unfold L5.u8_at. rewrite Z.add_0_r. cbn [nth rdn]. rewrite Hx. cbn. rewrite Z_to_bv_bv_unsigned. reflexivity.
    + cbn [nth]. replace (p + Z.of_nat (S i)) with (p + 1 + Z.of_nat i) by lia. apply Hb. cbn in Hi. lia.
Qed.
Lemma str_at_w_of : forall (M : mem) o r, PML.str_at M o r -> PML.str_at_w M o r.
Proof. intros M o [s|cap p s] H; [exact H | destruct H as (H1 & _ & H3); split; assumption]. Qed.

Definition FLD_PC : Z := 0x42ff4.
Definition fld_chk : bool :=
  match fetch_word RSEGS (Z_to_bv 64 FLD_PC) with
  | Some w => if is_ecall w then false else
              match decode_any w with
              | Some (FLoad FMT_D rd rs1 imm, sz) => (Z.eqb sz 4 && bv_eqb rd 10%bv && bv_eqb rs1 9%bv && Z.eqb (bv_signed imm) 24)%bool
              | _ => false end
  | None => false end.
Lemma fld_chk_ok : fld_chk = true.
Proof. vmc_refl. Qed.
Lemma vaddi_lit : forall a k, 0 <= a -> a + k < 2 ^ 64 -> 0 <= k -> v_addi (Z_to_bv 64 a) k = Z_to_bv 64 (a + k).
Proof.
  intros a k H0 H1 H2. unfold v_addi. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small a) by lia. reflexivity.
Qed.
Lemma bv_eqb_true : forall n (a b : bv n), bv_eqb a b = true -> a = b.
Proof. intros n a b H. apply bv_eq. unfold bv_eqb in H. apply Z.eqb_eq in H. exact H. Qed.
Lemma fld_step : forall (fx : FPState) R (M : mem) Ev bs, getr R 9%bv = Z_to_bv 64 Ev -> 0 <= Ev -> Ev + 32 < 2 ^ 64 ->
  rdn RSEGS M (Z_to_bv 64 (Ev + 24)) 8 = Some bs ->
  msteps RSEGS (@mkst fx R (Z_to_bv 64 FLD_PC) M (seg_rom RSEGS))
               (@mkst (mkFP (bvmap_set 10%bv (bv_extract 0 64 (le_bytes_to_word bs)) (@fp_regs fx)) (@fp_csr fx)) R (Z_to_bv 64 (FLD_PC + 4)) M (seg_rom RSEGS)).
Proof.
  intros fx R M Ev bs HV H0 H1 Hr. pose proof fld_chk_ok as C. unfold fld_chk in C.
  destruct (fetch_word RSEGS (Z_to_bv 64 FLD_PC)) as [w|] eqn:Hf; [|discriminate].
  destruct (is_ecall w) eqn:He; [discriminate|].
  destruct (decode_any w) as [[i sz]|] eqn:Hd; [|discriminate].
  destruct i; try discriminate. destruct fmt; try discriminate.
  apply andb_prop in C as [C C4]. apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2].
  apply Z.eqb_eq in C1, C4. apply bv_eqb_true in C2, C3. subst sz rd rs1.
  assert (Ha : v_addi (getr R 9%bv) (bv_signed imm) = Z_to_bv 64 (Ev + 24)) by (rewrite HV, C4; apply vaddi_lit; lia).
  pose proof (fp_step_fld fx RSEGS R (Z_to_bv 64 FLD_PC) M (seg_rom RSEGS) w 10%bv 9%bv imm (Z_to_bv 64 (Ev + 24)) bs Hf He Hd Ha Hr) as Hs.
  rewrite <- (vaddi_lit FLD_PC 4) by (unfold FLD_PC; lia). apply msteps_one; [reflexivity | exact Hs].
Qed.
Lemma u8_inj : forall (M : mem) a c1 c2, L5.u8_at RSEGS M a c1 -> L5.u8_at RSEGS M a c2 -> 0 <= c1 < 256 -> 0 <= c2 < 256 -> c1 = c2.
Proof.
  intros M a c1 c2 H1 H2 R1 R2. unfold L5.u8_at in *. rewrite H1 in H2.
  assert (X : Z_to_bv 8 c1 = Z_to_bv 8 c2) by congruence. clear H2. apply (f_equal (@bv_unsigned 8)) in X. rename X into H2. rewrite !Z_to_bv_unsigned in H2. unfold bv_wrap in H2. change (bv_modulus 8) with 256 in H2. rewrite !Z.mod_small in H2 by lia. exact H2.
Qed.

Lemma not_outside_w : forall F a, ~ L5.outside F a -> exists w, In w F /\ L5.in_rng w a.
Proof.
  induction F as [|w F IH]; intros a H; [exfalso; apply H; intros w []|].
  destruct (classic (L5.in_rng w a)) as [Y|N]; [exists w; split; [left; reflexivity | exact Y]|].
  destruct (IH a) as (w' & Hw' & Hi'); [intros X; apply H; intros w0 [<-|Hw0]; [exact N | exact (X w0 Hw0)] | exists w'; split; [right; exact Hw' | exact Hi']].
Qed.

Section HP.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Hypothesis LAY : PmLayout.pm0_layout L.
Lemma hp_start : forall LB sp SCR W (M : mem), L5C.stk (hl_sptop L) M sp SCR -> L5C.hpres L LB sp SCR W M M.
Proof. intros LB sp SCR W M (_ & _ & _ & _ & D). apply L5C.hpres_intro; [intros a _; reflexivity | exact D | intros a _ _ _ Hd; exact Hd]. Qed.
Lemma hp_weaken : forall LB sp SCR W W' (M M' : mem), L5C.hpres L LB sp SCR W M M' -> (forall a, L5.outside W' a -> L5.outside W a) -> L5C.hpres L LB sp SCR W' M M'.
Proof.
  intros LB sp SCR W W' M M' HP HW. apply L5C.hpres_intro.
  - intros a (Ha & HC & HE & HO). apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP). split; [exact Ha|]. split; [exact HC|]. split; [exact HE | exact (HW a HO)].
  - exact (L5C.hpres_defined _ _ _ _ _ _ _ HP).
  - intros a Ha HC HE Hd. exact (L5C.hpres_cdef _ _ _ _ _ _ _ a HP Ha HC HE Hd).
Qed.
Lemma hp_grow : forall LB sp SCR W (M0 M1 M2 : mem) (K : Z -> Prop), L5C.hpres L LB sp SCR W M0 M1 -> TK.samem K M1 M2 -> mem_grows M1 M2 ->
  TK2.blocks_ok L LB -> hl_ceil L + SCR <= sp -> 0x7fff80000000 <= hl_sptop L ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ K a -> (sp - SCR <= a < sp) \/ ~ L5.outside W a) -> L5C.hpres L LB sp SCR W M0 M2.
Proof.
  intros LB sp SCR W M0 M1 M2 K HP AG MG HB Hc Htop HK. apply L5C.hpres_intro.
  - intros a (Ha & HC & HE & HO). rewrite <- (L5C.hpres_kept _ _ _ _ _ _ _ a HP (conj Ha (conj HC (conj HE HO)))). apply AG; [exact Ha|].
    destruct (classic (K a)) as [Y|N]; [exact Y|]. exfalso. destruct (HK a Ha N) as [X|X]; [exact (TK2.client_not_window L LAY _ _ _ _ HC HB Hc Htop X) | exact (X HO)].
  - intros i Hi. apply MG. exact (L5C.hpres_defined _ _ _ _ _ _ _ HP i Hi).
  - intros a Ha HC HE Hd. apply MG. exact (L5C.hpres_cdef _ _ _ _ _ _ _ a HP Ha HC HE Hd).
Qed.
Lemma hp_call : forall LB sp SCR W (M0 M1 M2 : mem) LBk spc scr Wc, L5C.hpres L LB sp SCR W M0 M1 -> L5C.hpres L LBk spc scr Wc M1 M2 ->
  TK2.blocks_ok L LB -> incl LB LBk -> hl_ceil L + SCR <= sp -> 0x7fff80000000 <= hl_sptop L -> sp <= 2 ^ 47 -> sp - SCR <= spc - scr -> spc <= sp -> 0 <= scr ->
  (forall w a, In w Wc -> L5.in_rng w a -> (sp - SCR <= a < sp) \/ ~ L5.outside W a) -> L5C.hpres L LB sp SCR W M0 M2.
Proof.
  intros LB sp SCR W M0 M1 M2 LBk spc scr Wc HP HPc HB Hincl Hc Htop Hsp47 Hlo Hhi Hscr HW.
  pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_errno L LAY) as ERR.
  assert (CLc : forall a, 0 <= a < 2 ^ 64 -> client_addr L LB sp SCR a -> client_addr L LBk spc scr a).
  { intros a Ha HC. pose proof (TK2.client_not_window L LAY _ _ _ _ HC HB Hc Htop) as NW.
    destruct HC as [(b & Hb & Hr)|[(C1 & C2)|C]]; [left; exists b; split; [apply Hincl; exact Hb | exact Hr] | right; left; split; [exact C1 | lia] | right; right; exact C]. }
  apply L5C.hpres_intro.
  - intros a (Ha & HC & HE & HO). rewrite <- (L5C.hpres_kept _ _ _ _ _ _ _ a HP (conj Ha (conj HC (conj HE HO)))).
    apply (L5C.hpres_kept _ _ _ _ _ _ _ a HPc). split; [exact Ha|]. split; [exact (CLc a Ha HC)|]. split; [exact HE|].
    intros w Hw Hin. destruct (HW w a Hw Hin) as [X|X]; [exact (TK2.client_not_window L LAY _ _ _ _ HC HB Hc Htop X) | exact (X HO)].
  - intros i Hi. destruct (Z_le_dec (spc - scr) (sp - SCR + i)) as [G1|G1]; [destruct (Z_lt_dec (sp - SCR + i) spc) as [G2|G2]|].
    + pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HPc (sp - SCR + i - (spc - scr)) ltac:(lia)) as Y. replace (spc - scr + (sp - SCR + i - (spc - scr))) with (sp - SCR + i) in Y by lia. exact Y.
    + apply (L5C.hpres_cdef _ _ _ _ _ _ _ (sp - SCR + i) HPc); [unfold hl_ceil in *; lia | right; left; unfold hl_ceil in *; lia | unfold in_errno; rewrite ERR; unfold hl_ceil in *; lia | exact (L5C.hpres_defined _ _ _ _ _ _ _ HP i Hi)].
    + apply (L5C.hpres_cdef _ _ _ _ _ _ _ (sp - SCR + i) HPc); [unfold hl_ceil in *; lia | right; left; unfold hl_ceil in *; lia | unfold in_errno; rewrite ERR; unfold hl_ceil in *; lia | exact (L5C.hpres_defined _ _ _ _ _ _ _ HP i Hi)].
  - intros a Ha HC HE Hd. apply (L5C.hpres_cdef _ _ _ _ _ _ _ a HPc Ha (CLc a Ha HC) HE). exact (L5C.hpres_cdef _ _ _ _ _ _ _ a HP Ha HC HE Hd).
Qed.
End HP.

Section H.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Variable STRTOD_SCR : Z.
Hypothesis HSS : 0 <= STRTOD_SCR.
Hypothesis STRINIT2 : PMCS.strinit2_spec L HI.
Hypothesis CSTR : PMCS.cstr_ctor_spec L HI.
Hypothesis FROMU : PMFC.from_integer_u64_spec L HI.
Hypothesis FROMI : PMFC.from_integer_i64_spec L HI.
Hypothesis WD : PMFC.write_double_spec L HI STRTOD_SCR.
Hypothesis CONV : PMS.conv_ec_spec L.

Section K.
Variables (LB : list (Z * Z)) (cr : credit) (o V E sp r : Z) (g : PML.ls_state).
Variables (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model) (K : ShapeAlg.TSet).
Hypothesis HH : hi_heap HI LB cr M (m_vmmaps model).
Hypothesis Hh : m_halted model = None.
Hypothesis Hl : m_vm_lazy model = [].
Hypothesis Hmat : m_vm_materialized model = [].
Hypothesis HK0 : K [].
Hypothesis Hfp : PML.fp_ok fx.
Hypothesis Hra : getr R 1%bv = Z_to_bv 64 r.
Hypothesis Hrok : L5.ra_ok r.
Hypothesis Hsp : getr R 2%bv = Z_to_bv 64 sp.
Hypothesis Htp : getr R 4%bv = Z_to_bv 64 PML.TP.
Hypothesis STK : L5C.stk (hl_sptop L) M sp (PMCS.GETSTR_SCR STRTOD_SCR).
Hypothesis A0 : getr R 10%bv = Z_to_bv 64 o.
Hypothesis A1 : getr R 11%bv = Z_to_bv 64 (V + 8).
Hypothesis A3 : getr R 13%bv = Z_to_bv 64 E.
Hypothesis DV : L5.defined M V 48.
Hypothesis EC : PML.ec_at M E 0.
Hypothesis RO : PML.img_ro M.
Hypothesis LS : PML.ls_ok g M.
Hypothesis HG : g <> PML.LS0.
Hypothesis OO : PML.obj_on_stack L sp o 24.
Hypothesis DO : L5.defined M o 24.
Hypothesis OE : PML.obj_on_stack L sp E 16.
Hypothesis OV : PML.obj_on_stack L sp V 48.
Hypothesis AOE : box (o + 24 <= E \/ E + 16 <= o).
Hypothesis AOV : box (o + 24 <= V \/ V + 48 <= o).
Hypothesis AVE : box (V + 48 <= E \/ E + 16 <= V).
Definition W4 : list L5.range := [(o, 24); (E, 16); (0xd4df0, 2); (0xf6848, 544)].
Definition gpost (e : PMCUR.sevent) (M' : mem) (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (W : list L5.range) : Prop :=
  exists (code : Z) (g' : PML.ls_state),
    PMCS.s2_post L (Z.max 48 (match e with PMCUR.EvStr _ n | PMCUR.EvKey _ n => PML.str_cap n | _ => 0 end)) LB cr M' o LB' cr' /\ LBk = LB /\ PML.u32 M' E code /\ L5.defined M' E 16 /\ PML.ls_ok g' M' /\
    ((PMCS.conv_ok e /\ code = 0 /\ g' = g) \/ (~ PMCS.conv_ok e /\ code = 11 /\ g' = PML.regC g)) /\ W = W4.
Variable e : PMCUR.sevent.
Hypothesis EV : PMCUR.ev_at RSEGS M V e.
Hypothesis ES : PMCS.ev_src M LB e.
Hypothesis CR : credit_ok L cr (Z.max 48 (match e with PMCUR.EvStr _ n | PMCUR.EvKey _ n => PML.str_cap n | _ => 0 end)).
Hypothesis Hcont : forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (W : list L5.range),
  PML.fp_ok fx' -> gpost e M' LB' cr' LBk W -> regs_preserved R R' -> L5C.hpres L LBk sp (PMCS.GETSTR_SCR STRTOD_SCR) W M M' -> model_but_vm model model' ->
  hi_heap HI LB' cr' M' (m_vmmaps model') -> srealizes RSEGS SCFG (@PML.cfg fx' R' r M' model') K.

Lemma pre_ar : 2 ^ 40 <= o <= 2 ^ 47 - 24 /\ 2 ^ 12 <= V + 8 <= 2 ^ 47 - 40 /\ (o + 24 <= sp - 48 \/ sp <= o) /\ (V + 8 + 40 <= sp - 48 \/ sp <= V + 8) /\
  (V + 8 + 40 <= o \/ o + 24 <= V + 8) /\ CK.spok sp /\ L5.defined M (sp - 48) 48 /\ L5.defined M (V + 8 + 8) 16 /\
  2 ^ 40 <= E <= 2 ^ 47 - 16 /\ hl_ceil L + PMCS.GETSTR_SCR STRTOD_SCR <= sp /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 /\ sp <= hl_sptop L /\
  PMCS.GETSTR_SCR STRTOD_SCR = 10288 + STRTOD_SCR /\
  sp <= o /\ o + 24 <= hl_sptop L /\ sp <= E /\ E + 16 <= hl_sptop L /\ sp <= V /\ V + 48 <= hl_sptop L /\ sp mod 16 = 0.
Proof.
  pose proof STK as (S1 & S2 & S3 & S4 & S5). pose proof OO as (OO1 & OO2 & OO3). pose proof OE as (OE1 & OE2 & OE3). pose proof OV as (OV1 & OV2 & OV3).
  assert (HS : PMCS.GETSTR_SCR STRTOD_SCR = 10288 + STRTOD_SCR) by (unfold PMCS.GETSTR_SCR; lia).
  unfold box in AOV. unfold hl_ceil. rewrite HS in *.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [split; [lia | exact S1]|].
  split; [eapply L5.defined_sub; [exact S5 | lia | lia]|]. split; [eapply L5.defined_sub; [exact DV | lia | lia]|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact HS|]. repeat split; lia.
Qed.
Lemma u64_of_defined : forall (Mx : mem) a, L5.defined Mx a 8 -> exists v, 0 <= v < 2 ^ 64 /\ L5.u64_at RSEGS Mx a v.
Proof.
  intros Mx a Hd.
  destruct (bytes_of_defined Mx a 8 Hd) as (bs0 & _ & _).
  assert (RD : forall (k : nat) b, (forall i, 0 <= i < Z.of_nat k -> Mx (Z_to_bv 64 (b + i)) <> None) -> exists bs, rdn RSEGS Mx (Z_to_bv 64 b) k = Some bs /\ length bs = k).
  { induction k as [|k IH]; intros b H; [exists []; split; reflexivity|].
    destruct (IH (b + 1)) as (bs & Hr & Hl'); [intros i Hi; replace (b + 1 + i) with (b + (1 + i)) by lia; apply H; lia|].
    pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. destruct (Mx (Z_to_bv 64 b)) as [x|] eqn:Hb; [|contradiction].
    exists (x :: bs). cbn [rdn]. rewrite Hb, L5C.add1_lit, Hr. split; [reflexivity | cbn [length]; lia]. }
  destruct (RD 8%nat a Hd) as (bs & Hr & Hl'). exists (bytes_le_to_Z bs).
  pose proof (bytes_le_to_Z_nonneg bs) as N0. pose proof (bytes_le_to_Z_bound bs) as N1. rewrite Hl' in N1. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in N1.
  split; [lia|]. unfold L5.u64_at. rewrite Hr. f_equal. symmetry. apply APSX.word_to_le_bytes_of_bytes_n; [exact Hl' | lia].
Qed.

Lemma st_cov : forall Wa, (forall a, 0x10000 <= a < 0xf8000 -> L5.outside Wa a) -> TK2.statics_cov (L5C.kept L LB sp (PMCS.GETSTR_SCR STRTOD_SCR) Wa).
Proof.
  intros Wa HW. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_errno L LAY) as ERR.
  assert (X : forall a, 0x10000 <= a < 0xf8000 -> ~ (0xf6c08 <= a < 0xf6fb0) -> ~ (0xd675c <= a < 0xd6760) -> L5C.kept L LB sp (PMCS.GETSTR_SCR STRTOD_SCR) Wa a).
  { intros a Ha H1 H2. split; [lia|]. split; [right; right; rewrite ILO, IHI; split; [lia | intros Y; pose proof (PmLayout.ly_static L LAY a Y); lia]|].
    split; [unfold in_errno; rewrite ERR; lia | exact (HW a Ha)]. }
  split; [|split].
  - intros a (iv & Hiv & Hr). unfold PML.ll_foot_csrc in Hiv. apply X; repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd] in Hr; lia|]); destruct Hiv.
  - intros a Ha. unfold PML.IMG_RO_HI in Ha. apply X; lia.
  - intros a Ha. apply X; lia.
Qed.
Lemma samem_all_eq : forall (Ma Mb : mem), TK.samem (fun _ => True) Ma Mb -> Mb = Ma.
Proof.
  intros Ma Mb H. apply functional_extensionality. intros w. rewrite <- (Z_to_bv_bv_unsigned _ w). apply H; [|exact I].
  pose proof (bv_unsigned_in_range _ w) as X. change (bv_modulus 64) with (2 ^ 64) in X. exact X.
Qed.
Lemma csr_of_kog : forall R' : bvmap 5 word, TK.keepsR GSS.KOG R R' -> getr R' 8%bv = getr R 8%bv -> getr R' 9%bv = getr R 9%bv -> TK.keepsR CK.CSR R R'.
Proof.
  intros R' HK H8 H9 q Hq. unfold CK.CSR in Hq. cbn [In] in Hq.
  assert (QQ : forall m : nat, m = ridx q -> q = Z_to_bv 5 (Z.of_nat m)) by (intros m ->; symmetry; apply ridx_roundtrip).
  assert (HK' : In (ridx q) GSS.KOG -> getr R' q = getr R q) by (apply HK). unfold GSS.KOG in HK'. cbn [In] in HK'.
  repeat (destruct Hq as [Hq|Hq]; [first [apply HK'; tauto | rewrite (QQ _ Hq); assumption]|]). destruct Hq.
Qed.

Definition RETSTRETCH (pc : Z) : Prop := forall (fx : FPState) R M model K sp1 rav s0v s1v,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 48) -> CK.spok sp1 -> L5.ra_ok rav ->
  0 <= s0v < 2 ^ 64 -> 0 <= s1v < 2 ^ 64 -> L5.u64_at RSEGS M (sp1 - 8) rav -> L5.u64_at RSEGS M (sp1 - 16) s0v -> L5.u64_at RSEGS M (sp1 - 24) s1v ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> getr R' 8%bv = Z_to_bv 64 s0v -> getr R' 9%bv = Z_to_bv 64 s1v ->
      TK.keepsR GSS.KOG R R' -> TK.samem (fun _ => True) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R pc M model) K.

Lemma fin_ret : forall pc, RETSTRETCH pc -> forall (fx2 : FPState) R2 (M2 : mem) model2 LB2 cr2 Wa,
  PML.fp_ok fx2 -> getr R2 2%bv = Z_to_bv 64 (sp - 48) -> TK.keepsR GSS.KOG R R2 ->
  L5.u64_at RSEGS M2 (sp - 8) r -> L5.u64_at RSEGS M2 (sp - 16) (bv_unsigned (getr R 8%bv)) -> L5.u64_at RSEGS M2 (sp - 24) (bv_unsigned (getr R 9%bv)) ->
  L5C.hpres L LB sp (PMCS.GETSTR_SCR STRTOD_SCR) Wa M M2 -> (forall a, L5.outside W4 a -> L5.outside Wa a) ->
  m_halted model2 = None -> m_vm_lazy model2 = [] -> model_but_vm model model2 -> hi_heap HI LB2 cr2 M2 (m_vmmaps model2) -> gpost e M2 LB2 cr2 LB W4 ->
  srealizes RSEGS SCFG (@PML.cfg fx2 R2 pc M2 model2) K.
Proof.
  intros pc SR fx2 R2 M2 model2 LB2 cr2 Wa Hfp2 H2b KO2 F8 F16 F24 HP2 HW Hh2 Hl2 BV2 HH2 GP.
  pose proof pre_ar as (_ & _ & _ & _ & _ & SPOK & _).
  pose proof (bv_unsigned_in_range _ (getr R 8%bv)) as G8. pose proof (bv_unsigned_in_range _ (getr R 9%bv)) as G9. change (bv_modulus 64) with (2 ^ 64) in G8, G9.
  apply (SR fx2 R2 M2 model2 K sp r _ _ Hh2 Hl2 Hfp2 H2b SPOK Hrok G8 G9 F8 F16 F24).
  intros fx3 R3 M3 Hfp3 H2c H8c H9c KO3 AG3 MG3. pose proof (samem_all_eq _ _ AG3) as ->.
  apply (Hcont fx3 R3 M2 model2 LB2 cr2 LB W4 Hfp3 GP).
  - apply CK.rp_of_keeps; [rewrite H2c, Hsp; reflexivity|]. apply csr_of_kog; [exact (TK.keepsR_trans _ _ _ _ KO2 KO3) | rewrite H8c; apply Z_to_bv_bv_unsigned | rewrite H9c; apply Z_to_bv_bv_unsigned].
  - exact (hp_weaken L _ _ _ _ _ _ _ HP2 HW).
  - exact BV2.
  - exact HH2.
Qed.
Lemma ko_rp : forall qs R1 R2, regs_preserved R1 R2 -> forallb (fun q => existsb (Nat.eqb q) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat) qs = true -> TK.keepsR qs R1 R2.
Proof.
  intros qs R1 R2 RP Hqs. apply TK.keepsR_preserved; [exact RP|]. intros q Hq. rewrite forallb_forall in Hqs. specialize (Hqs _ Hq). apply existsb_exists in Hqs as (x & Hx & Eq).
  apply Nat.eqb_eq in Eq. subst x. unfold callee_saved_idx in *. cbn [In] in *. intuition (subst; cbn; tauto).
Qed.

Lemma after_entry : forall (R1 : bvmap 5 word) (M1 : mem), TK.samem (GSS.KEG sp o) M M1 -> mem_grows M M1 -> TK.keepsR GSS.KOG R R1 ->
  hi_heap HI LB cr M1 (m_vmmaps model) /\ L5C.hpres L LB sp (PMCS.GETSTR_SCR STRTOD_SCR) [(o, 24)] M M1 /\ PML.img_ro M1 /\ getr R1 4%bv = Z_to_bv 64 PML.TP /\
  L5.defined M1 o 24 /\ (forall scr, 0 <= scr -> 48 + scr <= PMCS.GETSTR_SCR STRTOD_SCR -> L5C.stk (hl_sptop L) M1 (sp - 48) scr) /\ TK2.blocks_ok L LB.
Proof.
  intros R1 M1 AG1 MG1 KO1. pose proof pre_ar as (Ho & HEv & D1 & D2 & D3 & SPOK & DF & D8 & HE & HC & HT & HS & HSCR & OO1 & OO2 & _).
  pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH) as BOK.
  split; [apply (TK2.heap_stack_write L HI HIok LAY _ _ M M1 _ (sp - 64) (hl_sptop L) HH ltac:(lia) ltac:(unfold hl_ceil in *; lia) ltac:(lia)); [|exact MG1];
          apply (TK.samem_weaken _ _ _ _ AG1); intros a Ha; unfold GSS.KEG; lia|].
  split; [apply (hp_grow L LAY LB sp _ _ M M M1 _ (hp_start L LB sp _ _ M STK) AG1 MG1 BOK HC (proj1 HT)); intros a Ha Hk; unfold GSS.KEG in Hk;
          destruct (classic (sp - 64 <= a < sp)) as [Y|N]; [left; lia | right; intros HO; apply (HO (o, 24) (or_introl eq_refl)); unfold L5.in_rng; cbn [fst snd]; lia]|].
  split; [apply (TK.img_clear_samem _ M M1 _ _ AG1); [lia | unfold PML.IMG_RO_HI; lia | intros i Hi; unfold PML.IMG_RO_HI in Hi; unfold GSS.KEG; lia | exact RO]|].
  split; [rewrite (KO1 4%bv ltac:(ck_in)); exact Htp|].
  split; [exact (L5.defined_grows _ _ _ _ MG1 DO)|].
  split; [intros scr H0 H1; apply (CK.sub_stk _ M M1 sp _ _ _ STK MG1); [apply CK.al16; [exact (proj2 SPOK) | reflexivity] | lia | lia | exact H0] | exact BOK].
Qed.

Lemma after_call : forall (M1 M2 : mem) scr s0 s1, L5C.hpres L LB sp (PMCS.GETSTR_SCR STRTOD_SCR) [(o, 24)] M M1 -> L5C.hpres L LB (sp - 48) scr [(o, 24)] M1 M2 ->
  0 <= scr -> 48 + scr <= PMCS.GETSTR_SCR STRTOD_SCR -> L5C.stk (hl_sptop L) M1 (sp - 48) scr ->
  L5.u64_at RSEGS M1 (sp - 8) r -> L5.u64_at RSEGS M1 (sp - 16) s0 -> L5.u64_at RSEGS M1 (sp - 24) s1 ->
  L5C.hpres L LB sp (PMCS.GETSTR_SCR STRTOD_SCR) [(o, 24)] M M2 /\ L5.u64_at RSEGS M2 (sp - 8) r /\ L5.u64_at RSEGS M2 (sp - 16) s0 /\ L5.u64_at RSEGS M2 (sp - 24) s1.
Proof.
  intros M1 M2 scr s0 s1 HP1 HPc Hs0 Hs1 STK1 F8 F16 F24. pose proof pre_ar as (Ho & HEv & D1 & D2 & D3 & SPOK & DF & D8 & HE & HC & HT & HS & HSCR & OO1 & OO2 & _).
  pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH) as BOK.
  pose proof (TK2.hpres_samem L LAY _ _ _ _ M1 M2 HPc BOK STK1 Hs0) as AG2.
  assert (KF : forall a, sp - 24 <= a < sp -> TK2.keepH L LB [(o, 24)] (sp - 48) scr a).
  { intros a Ha. split; [intros w [<-|[]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; lia | left; lia]. }
  split; [apply (hp_call L LAY LB sp _ _ M M1 M2 LB (sp - 48) scr _ HP1 HPc BOK (incl_refl _) HC (proj1 HT) ltac:(lia) ltac:(lia) ltac:(lia) Hs0);
          intros w a [<-|[]] Hin; right; intros HO; exact (HO (o, 24) (or_introl eq_refl) Hin)|].
  split; [apply (TK.u64_samem _ M1 M2 _ _ AG2); [lia | intros i Hi; apply KF; lia | exact F8]|].
  split; [apply (TK.u64_samem _ M1 M2 _ _ AG2); [lia | intros i Hi; apply KF; lia | exact F16]|].
  apply (TK.u64_samem _ M1 M2 _ _ AG2); [lia | intros i Hi; apply KF; lia | exact F24].
Qed.

Lemma gpost0 : forall (M2 : mem) LB2 cr2, L5C.hpres L LB sp (PMCS.GETSTR_SCR STRTOD_SCR) [(o, 24)] M M2 -> PMCS.s2_post L (Z.max 48 (match e with PMCUR.EvStr _ n | PMCUR.EvKey _ n => PML.str_cap n | _ => 0 end)) LB cr M2 o LB2 cr2 -> PMCS.conv_ok e ->
  gpost e M2 LB2 cr2 LB W4.
Proof.
  intros M2 LB2 cr2 HP S2 CO. pose proof pre_ar as (Ho & HEv & D1 & D2 & D3 & SPOK & DF & D8 & HE & HC & HT & HS & HSCR & OO1 & OO2 & OE1 & OE2 & _).
  pose proof (PmLayout.ly_errno L LAY) as ERR.
  assert (AG : TK.samem (L5C.kept L LB sp (PMCS.GETSTR_SCR STRTOD_SCR) [(o, 24)]) M M2) by (intros a Ha Hk; exact (L5C.hpres_kept _ _ _ _ _ _ _ a HP Hk)).
  assert (KE : forall i, E <= i < E + 16 -> L5C.kept L LB sp (PMCS.GETSTR_SCR STRTOD_SCR) [(o, 24)] i).
  { intros i Hi. unfold box in AOE. split; [lia|]. split; [right; left; unfold hl_ceil in *; lia|]. split; [unfold in_errno; rewrite ERR; lia|].
    intros w [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. lia. }
  destruct EC as (EC1 & EC2 & _).
  exists 0, g. split; [exact S2|]. split; [reflexivity|].
  split; [apply (TK.u32_samem _ M M2 _ _ AG); [lia | intros i Hi; apply KE; lia | exact EC1]|].
  split; [apply (TK.defined_samem _ M M2 _ _ AG); [lia | lia | exact KE | exact EC2]|].
  split; [apply (TK2.ls_ok_x _ M M2 AG); [apply st_cov; intros a Ha w [<-|[]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; lia | exact LS]|].
  split; [left; split; [exact CO | split; reflexivity] | reflexivity].
Qed.
Lemma s2_short : forall capb (M2 : mem) s, PML.str_at_w M2 o (PML.SShort s) -> PMCS.s2_post L capb LB cr M2 o LB cr.
Proof. intros capb M2 s H. exists (PML.SShort s). split; [exact H|]. split; [reflexivity|]. split; [intros _; reflexivity | intros b []]. Qed.
Lemma s2_long : forall capb (M2 : mem) cap p s, cap <= capb -> PML.str_at_w M2 o (PML.SLong cap p s) -> L5C.fresh_block L LB M2 p cap -> PMCS.s2_post L capb LB cr M2 o ((p, cap) :: LB) (debit L cr cap).
Proof. intros capb M2 cap p s Hc H F. exists (PML.SLong cap p s). split; [exact H|]. split; [reflexivity|]. split; [intros X; discriminate X | intros b [<-|[]]; split; [exact F | split; [reflexivity | exact Hc]]]. Qed.

Lemma arm_null : e = PMCUR.EvNull -> srealizes RSEGS SCFG (@PML.cfg fx R PMCS.PC_GET_STRING M model) K.
Proof using All.
  intros He. pose proof EV as EV0. rewrite He in EV0. destruct EV0 as (_ & F0).
  pose proof pre_ar as (Ho & HEv & D1 & D2 & D3 & SPOK & DF & D8 & HE & HC & HT & HS & HSCR & OO1 & OO2 & OE1 & OE2 & OV1 & OV2 & S16).
  destruct (u64_of_defined M (V + 8 + 24) ltac:(eapply L5.defined_sub; [exact DV | lia | lia])) as (v & Hv & V24).
  destruct (u64_of_defined M (V + 8 + 32) ltac:(eapply L5.defined_sub; [exact DV | lia | lia])) as (n & Hn & V32).
  apply (GSS.s_g_null FPM fx R M model K sp r o (V + 8) v n Hh Hl Hfp Hsp SPOK Hra Hrok A0 A1 Ho HEv D1 D2 D3 Hv Hn DF DO F0 D8 V24 V32 RO).
  intros fx1 R1 M1 Hfp1 H2a H1a H10a H11a H8a KO1 F8 F16 F24 AG1 MG1.
  destruct (after_entry R1 M1 AG1 MG1 KO1) as (HH1 & HP1 & RO1 & TP1 & DO1 & STK1 & BOK).
  assert (SC : 0 <= 64 + PMS.OPNEW_SCR /\ 48 + (64 + PMS.OPNEW_SCR) <= PMCS.GETSTR_SCR STRTOD_SCR) by (unfold PMS.OPNEW_SCR, PML.HEAP_STACK; lia).
  apply (CSTR LB cr o PMCS.STR_NULL (sp - 48) GST.R_CSTR [110; 117; 108; 108] fx1 R1 M1 model K HH1 (conj Hh (conj Hl Hmat)) HK0 Hfp1).
  { split; [exact (CK.mk_entry L R1 M1 (sp - 48) _ _ H1a (ra_ok_lit GST.R_CSTR eq_refl) H2a TP1 (STK1 _ (proj1 SC) (proj2 SC)))|].
    split; [exact H10a|]. split; [exact H11a|]. split; [left; reflexivity|]. split; [exact RO1|].
    split; [unfold PML.obj_on_stack; split; [lia | split; [lia | exact (proj2 (proj2 OO))]]|]. exact DO1. }
  intros fx2 R2 M2 model2 LB2 cr2 LBk2 W2 Hfp2 (-> & -> & SAT2 & -> & ->) RP2 HP2c BV2 HH2.
  destruct (after_call M1 M2 _ _ _ HP1 HP2c (proj1 SC) (proj2 SC) (STK1 _ (proj1 SC) (proj2 SC)) F8 F16 F24) as (HP2 & F8' & F16' & F24').
  apply (fin_ret GST.R_CSTR (GSS.s_g_rnull FPM) fx2 R2 M2 model2 LB cr [(o, 24)] Hfp2 ltac:(rewrite (RP2 2%bv ltac:(ck_in)); exact H2a)
           (TK.keepsR_trans _ _ _ _ KO1 (ko_rp GSS.KOG _ _ RP2 eq_refl)) F8' F16' F24' HP2).
  - intros a HO w [<-|[]] Hin. exact (HO (o, 24) (or_introl eq_refl) Hin).
  - rewrite (L5C.halted_but_vm _ _ BV2). exact Hh.
  - rewrite (L5C.lazy_but_vm _ _ BV2). exact Hl.
  - exact BV2.
  - exact HH2.
  - apply (gpost0 M2 LB cr HP2 (s2_short _ M2 _ SAT2)). rewrite He. exact I.
Qed.
Lemma arm_bool : forall b, e = PMCUR.EvBool b -> srealizes RSEGS SCFG (@PML.cfg fx R PMCS.PC_GET_STRING M model) K.
Proof using All.
  intros b He. pose proof EV as EV0. rewrite He in EV0. destruct EV0 as (_ & F0 & B0).
  pose proof pre_ar as (Ho & HEv & D1 & D2 & D3 & SPOK & DF & D8 & HE & HC & HT & HS & HSCR & OO1 & OO2 & OE1 & OE2 & OV1 & OV2 & S16).
  destruct (u64_of_defined M (V + 8 + 24) ltac:(eapply L5.defined_sub; [exact DV | lia | lia])) as (v & Hv & V24).
  destruct (u64_of_defined M (V + 8 + 32) ltac:(eapply L5.defined_sub; [exact DV | lia | lia])) as (n & Hn & V32).
  assert (VB : v mod 256 = if b then 1 else 0).
  { pose proof (TK2.u64_u8_low M (V + 8 + 24) v ltac:(lia) ltac:(lia) V24) as X. replace (V + 8 + 24) with (V + 32) in X by lia.
    apply (u8_inj M (V + 32)); [exact X | exact B0 | pose proof (Z.mod_pos_bound v 256 ltac:(lia)); lia | destruct b; lia]. }
  apply (GSS.s_g_bool FPM fx R M model K sp r o (V + 8) v n Hh Hl Hfp Hsp SPOK Hra Hrok A0 A1 Ho HEv D1 D2 D3 Hv Hn ltac:(rewrite VB; destruct b; lia) DF DO F0 D8 V24 V32 RO).
  intros fx1 R1 M1 Hfp1 H2a H1a H10a H11a H8a KO1 F8 F16 F24 AG1 MG1.
  destruct (after_entry R1 M1 AG1 MG1 KO1) as (HH1 & HP1 & RO1 & TP1 & DO1 & STK1 & BOK).
  assert (SC : 0 <= 64 + PMS.OPNEW_SCR /\ 48 + (64 + PMS.OPNEW_SCR) <= PMCS.GETSTR_SCR STRTOD_SCR) by (unfold PMS.OPNEW_SCR, PML.HEAP_STACK; lia).
  rewrite VB in H11a.
  apply (CSTR LB cr o (if b then PMCS.STR_TRUE else PMCS.STR_FALSE) (sp - 48) GST.R_CSTR (if b then [116; 114; 117; 101] else [102; 97; 108; 115; 101])
           fx1 R1 M1 model K HH1 (conj Hh (conj Hl Hmat)) HK0 Hfp1).
  { split; [exact (CK.mk_entry L R1 M1 (sp - 48) _ _ H1a (ra_ok_lit GST.R_CSTR eq_refl) H2a TP1 (STK1 _ (proj1 SC) (proj2 SC)))|].
    split; [exact H10a|]. split; [destruct b; exact H11a|]. split; [destruct b; [right; left; reflexivity | right; right; left; reflexivity]|]. split; [exact RO1|].
    split; [unfold PML.obj_on_stack; split; [lia | split; [lia | exact (proj2 (proj2 OO))]]|]. exact DO1. }
  intros fx2 R2 M2 model2 LB2 cr2 LBk2 W2 Hfp2 (-> & -> & SAT2 & -> & ->) RP2 HP2c BV2 HH2.
  destruct (after_call M1 M2 _ _ _ HP1 HP2c (proj1 SC) (proj2 SC) (STK1 _ (proj1 SC) (proj2 SC)) F8 F16 F24) as (HP2 & F8' & F16' & F24').
  apply (fin_ret GST.R_CSTR (GSS.s_g_rbool FPM) fx2 R2 M2 model2 LB cr [(o, 24)] Hfp2 ltac:(rewrite (RP2 2%bv ltac:(ck_in)); exact H2a)
           (TK.keepsR_trans _ _ _ _ KO1 (ko_rp GSS.KOG _ _ RP2 eq_refl)) F8' F16' F24' HP2).
  - intros a HO w [<-|[]] Hin. exact (HO (o, 24) (or_introl eq_refl) Hin).
  - rewrite (L5C.halted_but_vm _ _ BV2). exact Hh.
  - rewrite (L5C.lazy_but_vm _ _ BV2). exact Hl.
  - exact BV2.
  - exact HH2.
  - apply (gpost0 M2 LB cr HP2 (s2_short _ M2 _ SAT2)). rewrite He. exact I.
Qed.

Lemma arm_text : forall p n, (e = PMCUR.EvStr p n \/ e = PMCUR.EvKey p n) ->
  (forall fx R M model K sp1 rav o Ev v n', m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx ->
    getr R 2%bv = Z_to_bv 64 sp1 -> CK.spok sp1 -> getr R 1%bv = Z_to_bv 64 rav -> L5.ra_ok rav -> getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 Ev ->
    2 ^ 40 <= o <= 2 ^ 47 - 24 -> 2 ^ 12 <= Ev <= 2 ^ 47 - 40 -> (o + 24 <= sp1 - 48 \/ sp1 <= o) -> (Ev + 40 <= sp1 - 48 \/ sp1 <= Ev) -> (Ev + 40 <= o \/ o + 24 <= Ev) ->
    0 <= v < 2 ^ 64 -> 0 <= n' < 2 ^ 64 ->
    L5.defined M (sp1 - 48) 48 -> L5.defined M o 24 -> L5.u64_at RSEGS M Ev (match e with PMCUR.EvKey _ _ => 4097 | _ => 1 end) -> L5.defined M (Ev + 8) 16 ->
    L5.u64_at RSEGS M (Ev + 24) v -> L5.u64_at RSEGS M (Ev + 32) n' -> PML.img_ro M ->
    (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 48) -> getr R' 1%bv = Z_to_bv 64 GST.R_STR ->
        getr R' 10%bv = Z_to_bv 64 o -> getr R' 11%bv = Z_to_bv 64 v -> getr R' 12%bv = Z_to_bv 64 n' -> getr R' 8%bv = Z_to_bv 64 o -> TK.keepsR GSS.KOG R R' ->
        L5.u64_at RSEGS M' (sp1 - 8) rav -> L5.u64_at RSEGS M' (sp1 - 16) (bv_unsigned (getr R 8%bv)) -> L5.u64_at RSEGS M' (sp1 - 24) (bv_unsigned (getr R 9%bv)) ->
        TK.samem (GSS.KEG sp1 o) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PMCS.PC_STRINIT2 M' model) K) ->
    srealizes RSEGS SCFG (@PML.cfg fx R PMCS.PC_GET_STRING M model) K) ->
  RETSTRETCH GST.R_STR -> srealizes RSEGS SCFG (@PML.cfg fx R PMCS.PC_GET_STRING M model) K.
Proof using All.
  intros p n He SE SR.
  assert (EVt : L5.u64_at RSEGS M (V + 8) (match e with PMCUR.EvKey _ _ => 4097 | _ => 1 end) /\ L5.u64_at RSEGS M (V + 32) p /\ L5.u64_at RSEGS M (V + 40) n).
  { pose proof EV as EV0. destruct He as [He|He]; rewrite He in EV0 |- *; destruct EV0 as (_ & X1 & X2 & X3); (split; [exact X1 | split; assumption]). }
  assert (ESt : 0 <= n < 2 ^ 26 /\ L5.defined M p n /\ (n = 0 \/ exists b0, In b0 LB /\ fst b0 <= p /\ p + n <= fst b0 + snd b0)).
  { pose proof ES as ES0. destruct He as [He|He]; rewrite He in ES0; exact ES0. }
  assert (CRt : credit_ok L cr (Z.max 48 (PML.str_cap n))) by (pose proof CR as X; destruct He as [He|He]; rewrite He in X; exact X).
  destruct EVt as (F0 & V24 & V32). destruct ESt as (Hn & Dp & Hin).
  pose proof pre_ar as (Ho & HEv & D1 & D2 & D3 & SPOK & DF & D8 & HE & HC & HT & HS & HSCR & OO1 & OO2 & OE1 & OE2 & OV1 & OV2 & S16).
  pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH) as BOK0.

  destruct (bytes_of_defined M p (Z.to_nat n) ltac:(intros i Hi; apply Dp; lia)) as (txt & Hlt & Btx).
  assert (Hln : Z.of_nat (length txt) = n) by lia.

  assert (Hp : 0 <= p < 2 ^ 64 \/ n = 0).
  { destruct Hin as [->|(b0 & Hb0 & Q1 & Q2)]; [right; reflexivity | left]. destruct (BOK0 b0 Hb0) as (B0 & B1 & B2 & B3 & B4). unfold hl_ceil in B4. lia. }
  destruct (u64_of_defined M (V + 8 + 24) ltac:(eapply L5.defined_sub; [exact DV | lia | lia])) as (v & Hv & V24').
  assert (Hvp : v = p \/ n = 0).
  { destruct Hp as [Hp|Hp]; [left | right; exact Hp]. replace (V + 8 + 24) with (V + 32) in V24' by lia.
    unfold L5.u64_at in V24, V24'. rewrite V24 in V24'.
    assert (X : word_to_le_bytes 8 (Z_to_bv 64 p) = word_to_le_bytes 8 (Z_to_bv 64 v)) by congruence. clear V24'. apply (f_equal bytes_le_to_Z) in X. unfold word_to_le_bytes in X.
    rewrite !u64_of_Z in X by lia. rewrite !bytes_le_to_Z_of_le_bytes in X by lia. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in X. rewrite ?Z.mod_small in X by lia. lia. }
  assert (Hn64 : 0 <= n < 2 ^ 64) by lia.
  apply (SE fx R M model K sp r o (V + 8) v n Hh Hl Hfp Hsp SPOK Hra Hrok A0 A1 Ho HEv D1 D2 D3 Hv Hn64 DF DO F0 D8 V24'
           ltac:(replace (V + 8 + 32) with (V + 40) by lia; exact V32) RO).
  intros fx1 R1 M1 Hfp1 H2a H1a H10a H11a H12a H8a KO1 F8 F16 F24 AG1 MG1.
  destruct (after_entry R1 M1 AG1 MG1 KO1) as (HH1 & HP1 & RO1 & TP1 & DO1 & STK1 & BOK).
  assert (SC : 0 <= 48 + PMS.OPNEW_SCR /\ 48 + (48 + PMS.OPNEW_SCR) <= PMCS.GETSTR_SCR STRTOD_SCR) by (unfold PMS.OPNEW_SCR, PML.HEAP_STACK; lia).
  assert (Btx1 : L5.bytes_at RSEGS M1 v txt).
  { destruct Hin as [Hn0|(b0 & Hb0 & Q1 & Q2)].
    - rewrite Hn0 in Hlt. destruct txt; [intros i Hi; cbn in Hi; lia | cbn in Hlt; lia].
    - destruct (BOK0 b0 Hb0) as (B0 & B1 & B2 & B3 & B4). unfold hl_ceil in B4. destruct Hvp as [->|Hn0]; [|rewrite Hn0 in Hlt; destruct txt; [intros i Hi; cbn in Hi; lia | cbn in Hlt; lia]].
      apply (TK.bytes_samem _ M M1 p txt AG1); [lia | lia | intros i Hi; unfold GSS.KEG; lia | exact Btx]. }
  assert (Dtx1 : L5.defined M1 v (Z.of_nat (length txt))).
  { rewrite Hln. destruct Hvp as [->|Hn0]; [exact (L5.defined_grows _ _ _ _ MG1 Dp) | intros i Hi; lia]. }
  apply (STRINIT2 LB cr o v (sp - 48) GST.R_STR txt fx1 R1 M1 model K HH1 (conj Hh (conj Hl Hmat)) HK0 Hfp1).
  { split; [exact (CK.mk_entry L R1 M1 (sp - 48) _ _ H1a (ra_ok_lit GST.R_STR eq_refl) H2a TP1 (STK1 _ (proj1 SC) (proj2 SC)))|].
    split; [exact H10a|]. split; [exact H11a|]. split; [unfold PML.a2; rewrite Hln; exact H12a|]. split; [lia|]. split; [exact Btx1|]. split; [exact Dtx1|].
    split; [unfold PML.obj_on_stack; split; [lia | split; [lia | exact (proj2 (proj2 OO))]]|]. split; [exact DO1|].
    split; [destruct Hin as [Hn0|(b0 & Hb0 & Q1 & Q2)]; [left; rewrite Hn0 in Hlt; destruct txt; [reflexivity | cbn in Hlt; lia]
                                                      | destruct Hvp as [->|Hn0]; [right; exists b0; rewrite Hln; split; [exact Hb0 | lia] | left; rewrite Hn0 in Hlt; destruct txt; [reflexivity | cbn in Hlt; lia]]]|].
    intros H23. destruct CRt as (C1 & C2). rewrite Hln. split; [exact C1 | lia]. }
  intros fx2 R2 M2 model2 LB2 cr2 LBk2 W2 Hfp2 (-> & -> & POST) RP2 HP2c BV2 HH2.
  destruct (after_call M1 M2 _ _ _ HP1 HP2c (proj1 SC) (proj2 SC) (STK1 _ (proj1 SC) (proj2 SC)) F8 F16 F24) as (HP2 & F8' & F16' & F24').
  apply (fin_ret GST.R_STR SR fx2 R2 M2 model2 LB2 cr2 [(o, 24)] Hfp2 ltac:(rewrite (RP2 2%bv ltac:(ck_in)); exact H2a)
           (TK.keepsR_trans _ _ _ _ KO1 (ko_rp GSS.KOG _ _ RP2 eq_refl)) F8' F16' F24' HP2).
  - intros a HO w [<-|[]] Hin'. exact (HO (o, 24) (or_introl eq_refl) Hin').
  - rewrite (L5C.halted_but_vm _ _ BV2). exact Hh.
  - rewrite (L5C.lazy_but_vm _ _ BV2). exact Hl.
  - exact BV2.
  - exact HH2.
  - apply (gpost0 M2 LB2 cr2 HP2); [|destruct He as [He|He]; rewrite He; exact I].
    destruct POST as [(_ & SAT & -> & ->)|(_ & p' & SAT & FB & -> & ->)]; [exact (s2_short _ M2 _ SAT) | refine (s2_long _ M2 _ _ _ _ SAT FB); rewrite Hln; destruct He as [He|He]; rewrite He; apply Z.le_max_r].
Qed.

Lemma arm_int : forall flags rpc cpc, L5.u64_at RSEGS M (V + 8) flags -> PMCS.conv_ok e -> L5.ra_ok rpc ->
  (forall fx R M model K sp1 rav o Ev v n, m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx ->
    getr R 2%bv = Z_to_bv 64 sp1 -> CK.spok sp1 -> getr R 1%bv = Z_to_bv 64 rav -> L5.ra_ok rav -> getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 Ev ->
    2 ^ 40 <= o <= 2 ^ 47 - 24 -> 2 ^ 12 <= Ev <= 2 ^ 47 - 40 -> (o + 24 <= sp1 - 48 \/ sp1 <= o) -> (Ev + 40 <= sp1 - 48 \/ sp1 <= Ev) -> (Ev + 40 <= o \/ o + 24 <= Ev) ->
    0 <= v < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
    L5.defined M (sp1 - 48) 48 -> L5.defined M o 24 -> L5.u64_at RSEGS M Ev flags -> L5.defined M (Ev + 8) 16 -> L5.u64_at RSEGS M (Ev + 24) v -> L5.u64_at RSEGS M (Ev + 32) n ->
    PML.img_ro M ->
    (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 48) -> getr R' 1%bv = Z_to_bv 64 rpc ->
        getr R' 10%bv = Z_to_bv 64 v -> getr R' 11%bv = Z_to_bv 64 o -> getr R' 8%bv = Z_to_bv 64 o -> TK.keepsR GSS.KOG R R' ->
        L5.u64_at RSEGS M' (sp1 - 8) rav -> L5.u64_at RSEGS M' (sp1 - 16) (bv_unsigned (getr R 8%bv)) -> L5.u64_at RSEGS M' (sp1 - 24) (bv_unsigned (getr R 9%bv)) ->
        L5.u64_at RSEGS M' o 0 -> L5.u64_at RSEGS M' (o + 8) 0 -> L5.u64_at RSEGS M' (o + 16) 0 -> TK.samem (GSS.KEG sp1 o) M M' -> mem_grows M M' ->
        srealizes RSEGS SCFG (@PML.cfg fx' R' cpc M' model) K) ->
    srealizes RSEGS SCFG (@PML.cfg fx R PMCS.PC_GET_STRING M model) K) ->
  RETSTRETCH rpc -> PMFC.from_integer_spec L HI cpc (fun v => 0 <= v < 2 ^ 64) -> srealizes RSEGS SCFG (@PML.cfg fx R PMCS.PC_GET_STRING M model) K.
Proof using All.
  intros flags rpc cpc F0 CO HRA SE SR FROM.
  pose proof pre_ar as (Ho & HEv & D1 & D2 & D3 & SPOK & DF & D8 & HE & HC & HT & HS & HSCR & OO1 & OO2 & OE1 & OE2 & OV1 & OV2 & S16).
  destruct (u64_of_defined M (V + 8 + 24) ltac:(eapply L5.defined_sub; [exact DV | lia | lia])) as (v & Hv & V24).
  destruct (u64_of_defined M (V + 8 + 32) ltac:(eapply L5.defined_sub; [exact DV | lia | lia])) as (n & Hn & V32).
  apply (SE fx R M model K sp r o (V + 8) v n Hh Hl Hfp Hsp SPOK Hra Hrok A0 A1 Ho HEv D1 D2 D3 Hv Hn DF DO F0 D8 V24 V32 RO).
  intros fx1 R1 M1 Hfp1 H2a H1a H10a H11a H8a KO1 F8 F16 F24 Z0 Z8 Z16 AG1 MG1.
  destruct (after_entry R1 M1 AG1 MG1 KO1) as (HH1 & HP1 & RO1 & TP1 & DO1 & STK1 & BOK).
  assert (SC : 0 <= PMFC.FROMINT_SCR /\ 48 + PMFC.FROMINT_SCR <= PMCS.GETSTR_SCR STRTOD_SCR) by (unfold PMFC.FROMINT_SCR, PMFC.STR_SCR, PMS.STR_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK; lia).
  apply (FROM LB cr o v (sp - 48) rpc fx1 R1 M1 model K HH1 (conj Hh (conj Hl Hmat)) HK0 Hfp1).
  { split; [exact (CK.mk_entry L R1 M1 (sp - 48) _ _ H1a HRA H2a TP1 (STK1 _ (proj1 SC) (proj2 SC)))|].
    split; [exact H10a|]. split; [exact Hv|]. split; [exact H11a|]. split; [exact (sso_empty_of_zero M1 o ltac:(lia) ltac:(lia) Z0)|]. split; [exact DO1|].
    split; [unfold PML.obj_on_stack; split; [lia | split; [lia | exact (proj2 (proj2 OO))]]|]. exact RO1. }
  intros fx2 R2 M2 model2 LB2 cr2 LBk2 W2 Hfp2 (d & _ & SAT2 & _ & -> & -> & -> & ->) RP2 HP2c BV2 HH2.
  destruct (after_call M1 M2 _ _ _ HP1 HP2c (proj1 SC) (proj2 SC) (STK1 _ (proj1 SC) (proj2 SC)) F8 F16 F24) as (HP2 & F8' & F16' & F24').
  apply (fin_ret rpc SR fx2 R2 M2 model2 LB cr [(o, 24)] Hfp2 ltac:(rewrite (RP2 2%bv ltac:(ck_in)); exact H2a)
           (TK.keepsR_trans _ _ _ _ KO1 (ko_rp GSS.KOG _ _ RP2 eq_refl)) F8' F16' F24' HP2).
  - intros a HO w [<-|[]] Hin. exact (HO (o, 24) (or_introl eq_refl) Hin).
  - rewrite (L5C.halted_but_vm _ _ BV2). exact Hh.
  - rewrite (L5C.lazy_but_vm _ _ BV2). exact Hl.
  - exact BV2.
  - exact HH2.
  - exact (gpost0 M2 LB cr HP2 (s2_short _ M2 _ (str_at_w_of _ _ _ SAT2)) CO).
Qed.

Lemma arm_dbl : forall x, e = PMCUR.EvDbl x -> srealizes RSEGS SCFG (@PML.cfg fx R PMCS.PC_GET_STRING M model) K.
Proof using All.
  intros x He. pose proof EV as EV0. rewrite He in EV0. destruct EV0 as (_ & F0 & _).
  assert (CR48 : credit_ok L cr 48) by (pose proof CR as X; rewrite He in X; exact X).
  pose proof pre_ar as (Ho & HEv & D1 & D2 & D3 & SPOK & DF & D8 & HE & HC & HT & HS & HSCR & OO1 & OO2 & OE1 & OE2 & OV1 & OV2 & S16).
  destruct (u64_of_defined M (V + 8 + 24) ltac:(eapply L5.defined_sub; [exact DV | lia | lia])) as (v & Hv & V24).
  destruct (u64_of_defined M (V + 8 + 32) ltac:(eapply L5.defined_sub; [exact DV | lia | lia])) as (n & Hn & V32).
  apply (GSS.s_g_dbl FPM fx R M model K sp r o (V + 8) v n Hh Hl Hfp Hsp SPOK Hra Hrok A0 A1 Ho HEv D1 D2 D3 Hv Hn
           ltac:(pose proof STK as (_ & _ & _ & _ & S5); rewrite HSCR in S5; eapply L5.defined_sub; [exact S5 | lia | lia]) ltac:(right; lia) ltac:(right; lia)
           DF DO F0 D8 V24 V32 RO).
  intros fx1 R1 M1 Hfp1 H2a H8a H9a KO1 F8 F16 F24 Z0 Z8 Z16 W0 W4' W8 AG1 MG1.
  destruct (after_entry R1 M1 AG1 MG1 KO1) as (HH1 & HP1 & RO1 & TP1 & DO1 & STK1 & BOK).

  assert (V24' : L5.u64_at RSEGS M1 (V + 8 + 24) v) by (apply (TK.u64_samem _ M M1 _ _ AG1); [lia | intros i Hi; unfold GSS.KEG; unfold box in AOV; lia | exact V24]).
  pose proof (fld_step fx1 R1 M1 (V + 8) _ H9a ltac:(lia) ltac:(lia) V24') as HMS.
  change GST.FLD with FLD_PC. unfold PML.cfg. apply (L5.cps_of_msteps _ _ _ _ _ _ _ _ _ _ _ Hh Hl HMS).
  pose proof (FPM _ _ _ _ _ _ _ _ HMS Hfp1) as Hfp1'. fold (@PML.cfg (mkFP (bvmap_set 10%bv (bv_extract 0 64 (le_bytes_to_word (word_to_le_bytes 8 (Z_to_bv 64 v)))) (@fp_regs fx1)) (@fp_csr fx1)) R1 (FLD_PC + 4) M1 model).
  change (FLD_PC + 4) with GST.WD_CALL.
  apply (GSS.s_g_wdcall FPM _ R1 M1 model K sp o Hh Hl Hfp1' H2a SPOK H8a ltac:(lia)).
  intros fx2 R2 M2 Hfp2 H2w H1w H10w H11w KS2 AGw MGw. pose proof (samem_all_eq _ _ AGw) as ->.
  assert (SC : 0 <= PMFC.WD_SCR STRTOD_SCR /\ 48 + PMFC.WD_SCR STRTOD_SCR <= PMCS.GETSTR_SCR STRTOD_SCR).
  { unfold PMFC.WD_SCR, PMFC.DTOA_TRUE_SCR, PMFC.DTOA_FALSE_SCR, PMFC.SNPRINTF_SCR, PMFC.STR_SCR, PMS.STR_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK. lia. }
  assert (TP2 : getr R2 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KS2 4%bv ltac:(ck_in)); exact TP1).
  apply (WD LB cr (sp - 40) o 46 (sp - 48) GST.R_WD fx2 R2 M1 model K HH1 (conj Hh (conj Hl Hmat)) HK0 Hfp2).
  { split; [exact (CK.mk_entry L R2 M1 (sp - 48) _ _ H1w (ra_ok_lit GST.R_WD eq_refl) H2w TP2 (STK1 _ (proj1 SC) (proj2 SC)))|].
    split; [exact H10w|]. split; [exact H11w|]. split; [lia|]. split; [destruct STK as (_ & _ & STK3 & _); lia|]. split; [exact W0|]. split; [replace (sp - 40 + 4) with (sp - 36) by lia; exact W4'|].
    split; [replace (sp - 40 + 8) with (sp - 32) by lia; exact W8|]. split; [exact (sso_empty_of_zero M1 o ltac:(lia) ltac:(lia) Z0)|]. split; [exact DO1|].
    split; [unfold PML.obj_on_stack; split; [lia | split; [lia | exact (proj2 (proj2 OO))]]|]. split; [exact RO1 | exact CR48]. }
  intros fx3 R3 M3 model3 LB3 cr3 LBk3 W3 Hfp3 (_ & (s' & _ & NS) & -> & ->) RP3 HP3c BV3 HH3.
  destruct (after_call M1 M3 _ _ _ HP1 HP3c (proj1 SC) (proj2 SC) (STK1 _ (proj1 SC) (proj2 SC)) F8 F16 F24) as (HP3 & F8' & F16' & F24').
  assert (KO3 : TK.keepsR GSS.KOG R R3).
  { apply (TK.keepsR_trans _ _ _ _ KO1). apply (TK.keepsR_trans _ _ _ _ (CK.keepsR_sub CK.CSR GSS.KOG _ _ KS2 ltac:(intros q Hq; unfold GSS.KOG in Hq; unfold CK.CSR; cbn [In] in Hq |- *; tauto))).
    exact (ko_rp GSS.KOG _ _ RP3 eq_refl). }
  apply (fin_ret GST.R_WD (GSS.s_g_rdbl FPM) fx3 R3 M3 model3 LB3 cr3 [(o, 24)] Hfp3 ltac:(rewrite (RP3 2%bv ltac:(ck_in)); exact H2w) KO3 F8' F16' F24' HP3).
  - intros a HO w [<-|[]] Hin. exact (HO (o, 24) (or_introl eq_refl) Hin).
  - rewrite (L5C.halted_but_vm _ _ BV3). exact Hh.
  - rewrite (L5C.lazy_but_vm _ _ BV3). exact Hl.
  - exact BV3.
  - exact HH3.
  - apply (gpost0 M3 LB3 cr3 HP3); [|rewrite He; exact I].
    destruct NS as [(_ & SAT & _ & -> & ->)|(p' & _ & SAT & _ & FB & -> & ->)]; [exact (s2_short _ M3 _ (str_at_w_of _ _ _ SAT)) | refine (s2_long _ M3 _ _ _ _ (str_at_w_of _ _ _ SAT) FB); rewrite He; apply Z.le_max_l].
Qed.

Lemma arm_cont : forall flags, L5.u64_at RSEGS M (V + 8) flags -> ~ PMCS.conv_ok e ->
  (forall fx R M model K sp1 rav o Ev v n, m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx ->
    getr R 2%bv = Z_to_bv 64 sp1 -> CK.spok sp1 -> getr R 1%bv = Z_to_bv 64 rav -> L5.ra_ok rav -> getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 Ev ->
    2 ^ 40 <= o <= 2 ^ 47 - 24 -> 2 ^ 12 <= Ev <= 2 ^ 47 - 40 -> (o + 24 <= sp1 - 48 \/ sp1 <= o) -> (Ev + 40 <= sp1 - 48 \/ sp1 <= Ev) -> (Ev + 40 <= o \/ o + 24 <= Ev) ->
    0 <= v < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
    L5.defined M (sp1 - 48) 48 -> L5.defined M o 24 -> L5.u64_at RSEGS M Ev flags -> L5.defined M (Ev + 8) 16 -> L5.u64_at RSEGS M (Ev + 24) v -> L5.u64_at RSEGS M (Ev + 32) n ->
    PML.img_ro M ->
    (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 48) -> getr R' 1%bv = Z_to_bv 64 GST.R_CONV ->
        getr R' 10%bv = getr R 13%bv -> getr R' 11%bv = Z_to_bv 64 11 -> getr R' 8%bv = Z_to_bv 64 o -> TK.keepsR GSS.KOG R R' ->
        L5.u64_at RSEGS M' (sp1 - 8) rav -> L5.u64_at RSEGS M' (sp1 - 16) (bv_unsigned (getr R 8%bv)) -> L5.u64_at RSEGS M' (sp1 - 24) (bv_unsigned (getr R 9%bv)) ->
        TK.samem (GSS.KEG sp1 o) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PMS.PC_CONV_EC M' model) K) ->
    srealizes RSEGS SCFG (@PML.cfg fx R PMCS.PC_GET_STRING M model) K) ->
  (forall (fx : FPState) R M model K sp1 rav s0v s1v o,
    m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 48) -> CK.spok sp1 -> L5.ra_ok rav -> getr R 8%bv = Z_to_bv 64 o ->
    0 <= s0v < 2 ^ 64 -> 0 <= s1v < 2 ^ 64 -> L5.u64_at RSEGS M (sp1 - 8) rav -> L5.u64_at RSEGS M (sp1 - 16) s0v -> L5.u64_at RSEGS M (sp1 - 24) s1v ->
    2 ^ 40 <= o <= 2 ^ 47 - 24 -> (o + 24 <= sp1 - 48 \/ sp1 <= o) -> L5.defined M o 24 ->
    (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> getr R' 8%bv = Z_to_bv 64 s0v -> getr R' 9%bv = Z_to_bv 64 s1v ->
        TK.keepsR GSS.KOG R R' -> L5.u64_at RSEGS M' o 0 -> L5.u64_at RSEGS M' (o + 8) 0 -> L5.u64_at RSEGS M' (o + 16) 0 ->
        TK.samem (fun a => ~ (o <= a < o + 24)) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
    srealizes RSEGS SCFG (@PML.cfg fx R GST.R_CONV M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PMCS.PC_GET_STRING M model) K.
Proof using All.
  intros flags F0 NC SE SR.
  pose proof pre_ar as (Ho & HEv & D1 & D2 & D3 & SPOK & DF & D8 & HE & HC & HT & HS & HSCR & OO1 & OO2 & OE1 & OE2 & OV1 & OV2 & S16).
  pose proof (PmLayout.ly_errno L LAY) as ERR.
  destruct (u64_of_defined M (V + 8 + 24) ltac:(eapply L5.defined_sub; [exact DV | lia | lia])) as (v & Hv & V24).
  destruct (u64_of_defined M (V + 8 + 32) ltac:(eapply L5.defined_sub; [exact DV | lia | lia])) as (n & Hn & V32).
  apply (SE fx R M model K sp r o (V + 8) v n Hh Hl Hfp Hsp SPOK Hra Hrok A0 A1 Ho HEv D1 D2 D3 Hv Hn DF DO F0 D8 V24 V32 RO).
  intros fx1 R1 M1 Hfp1 H2a H1a H10a H11a H8a KO1 F8 F16 F24 AG1 MG1.
  destruct (after_entry R1 M1 AG1 MG1 KO1) as (HH1 & HP1 & RO1 & TP1 & DO1 & STK1 & BOK).
  assert (SC : 0 <= PMS.SETEC_SCR /\ 48 + PMS.SETEC_SCR <= PMCS.GETSTR_SCR STRTOD_SCR) by (unfold PMS.SETEC_SCR; lia).
  assert (DE1 : L5.defined M1 E 16) by (destruct EC as (_ & X & _); exact (L5.defined_grows _ _ _ _ MG1 X)).
  assert (LS1 : PML.ls_ok g M1) by (apply (TK2.ls_ok_x _ M M1 AG1); [apply TK2.statics_cov_lo; intros a Ha; unfold GSS.KEG; lia | exact LS]).
  apply (CONV E 11 (sp - 48) GST.R_CONV g fx1 R1 M1 model K Hh Hl HK0 Hfp1).
  { split; [exact (CK.mk_entry L R1 M1 (sp - 48) _ _ H1a (ra_ok_lit GST.R_CONV eq_refl) H2a TP1 (STK1 _ (proj1 SC) (proj2 SC)))|].
    split; [unfold PML.a0; rewrite H10a; exact A3|]. split; [exact H11a|]. split; [lia|]. split; [exact DE1|].
    split; [unfold PML.obj_on_stack; split; [lia | split; [lia | exact (proj2 (proj2 OE))]]|]. split; [exact LS1 | exact HG]. }
  intros fx2 R2 M2 Hfp2 (ECC & LSC & _) RP2 FB2 MG2. pose proof (TK2.frame_but_samem _ _ _ FB2) as AG2.
  assert (KC : forall a, (sp - 24 <= a < sp) \/ (o <= a < o + 24) -> L5.outside ((sp - 48 - PMS.SETEC_SCR, PMS.SETEC_SCR) :: [(E, 16); (0xd4df0, 2); (0xf6848, 544)]) a).
  { intros a Ha w Hw Hin. unfold box in AOE. unfold L5.in_rng in Hin. unfold PMS.SETEC_SCR in Hw. destruct Hw as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hin; lia. }
  assert (F8' : L5.u64_at RSEGS M2 (sp - 8) r) by (apply (TK.u64_samem _ M1 M2 _ _ AG2); [lia | intros i Hi; apply KC; lia | exact F8]).
  assert (F16' : L5.u64_at RSEGS M2 (sp - 16) (bv_unsigned (getr R 8%bv))) by (apply (TK.u64_samem _ M1 M2 _ _ AG2); [lia | intros i Hi; apply KC; lia | exact F16]).
  assert (F24' : L5.u64_at RSEGS M2 (sp - 24) (bv_unsigned (getr R 9%bv))) by (apply (TK.u64_samem _ M1 M2 _ _ AG2); [lia | intros i Hi; apply KC; lia | exact F24]).
  assert (HP2 : L5C.hpres L LB sp (PMCS.GETSTR_SCR STRTOD_SCR) W4 M M2).
  { apply (hp_grow L LAY LB sp _ _ M M1 M2 _ (hp_weaken L _ _ _ [(o, 24)] W4 _ _ HP1 ltac:(intros a HO w [<-|[]] Hin; apply (HO (o, 24)); [unfold W4; left; reflexivity | exact Hin])) AG2 MG2 BOK HC (proj1 HT)).
    intros a Ha Hk. destruct (not_outside_w _ a Hk) as (w & Hw & Hin). unfold L5.in_rng in Hin. unfold PMS.SETEC_SCR in Hw.
    destruct Hw as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hin; [left; lia | right | right | right]; intros HO;
      [apply (HO (E, 16)) | apply (HO (0xd4df0, 2)) | apply (HO (0xf6848, 544))]; unfold W4; cbn [In]; first [tauto | unfold L5.in_rng; cbn [fst snd]; lia]. }
  assert (HH2 : hi_heap HI LB cr M2 (m_vmmaps model)).
  { apply (TK2.heap_pure_write L HI HIok LAY _ _ M1 M2 _ _ HH1 (proj1 HT) AG2 MG2). intros a Hz Ha. destruct (not_outside_w _ a Ha) as (w & Hw & Hin).
    unfold L5.in_rng in Hin. unfold PMS.SETEC_SCR in Hw. destruct Hw as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hin; [left; unfold hl_ceil in *; lia | left; unfold hl_ceil in *; lia | right; lia | right; lia]. }
  pose proof (bv_unsigned_in_range _ (getr R 8%bv)) as G8. pose proof (bv_unsigned_in_range _ (getr R 9%bv)) as G9. change (bv_modulus 64) with (2 ^ 64) in G8, G9.
  apply (SR fx2 R2 M2 model K sp r _ _ o Hh Hl Hfp2 ltac:(rewrite (RP2 2%bv ltac:(ck_in)); exact H2a) SPOK Hrok ltac:(rewrite (RP2 8%bv ltac:(ck_in)); exact H8a)
           G8 G9 F8' F16' F24' Ho D1 (L5.defined_grows _ _ _ _ MG2 DO1)).
  intros fx3 R3 M3 Hfp3 H2c H8c H9c KO3 Z0 Z8 Z16 AG3 MG3.
  apply (Hcont fx3 R3 M3 model LB cr LB W4 Hfp3).
  - destruct ECC as (EC1 & EC2 & _).
    assert (KE : forall i, E <= i < E + 16 -> ~ (o <= i < o + 24)) by (unfold box in AOE; intros i Hi; lia).
    exists 11, (PML.regC g). split; [exact (s2_short _ M3 [] (sso_empty_of_zero M3 o ltac:(lia) ltac:(lia) Z0))|]. split; [reflexivity|].
    split; [apply (TK.u32_samem _ M2 M3 _ _ AG3); [lia | intros i Hi; apply KE; lia | exact EC1]|].
    split; [exact (L5.defined_grows _ _ _ _ MG3 EC2)|].
    split; [apply (TK2.ls_ok_x _ M2 M3 AG3); [apply TK2.statics_cov_lo; intros a Ha; lia | exact LSC]|].
    split; [right; split; [exact NC | split; reflexivity] | reflexivity].
  - apply CK.rp_of_keeps; [rewrite H2c, Hsp; reflexivity|].
    apply csr_of_kog; [exact (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ KO1 (ko_rp GSS.KOG _ _ RP2 eq_refl)) KO3) | rewrite H8c; apply Z_to_bv_bv_unsigned | rewrite H9c; apply Z_to_bv_bv_unsigned].
  - apply (hp_grow L LAY LB sp _ _ M M2 M3 _ HP2 AG3 MG3 BOK HC (proj1 HT)). intros a Ha Hk. right. intros HO. apply (HO (o, 24)); [unfold W4; left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia].
  - exact (L5C.model_but_vm_refl model).
  - apply (TK2.heap_stack_write L HI HIok LAY _ _ M2 M3 _ (sp - 48) (hl_sptop L) HH2 ltac:(lia) ltac:(unfold hl_ceil in *; lia) ltac:(lia)); [|exact MG3].
    apply (TK.samem_weaken _ _ _ _ AG3). intros a Ha. lia.
Qed.
End K.

Theorem get_string_ok : PMCS.get_string_spec L HI STRTOD_SCR.
Proof.
  intros LB cr o V E sp r e g fx R M model K HH (Hh & Hl & Hmat) HK0 Hfp
    (EN & A0 & A1 & A3 & EV & ES & DV & EC & RO & LS & HG & OO & DO & OE & OV & AOE & AOV & AVE & CR) Hcont.
  destruct EN as (Hra & Hrok & Hsp & Htp & STK). unfold PML.a0, PML.a1, PML.a3, PML.apart in *.
  destruct e as [ | b | x | x | x | p n | p n | | | | ].
  - exact (arm_null LB cr o V E sp r g fx R M model K HH Hh Hl Hmat HK0 Hfp Hra Hrok Hsp Htp STK A0 A1 A3 DV EC RO LS HG OO DO OE OV AOE AOV AVE _ EV ES CR Hcont eq_refl).
  - exact (arm_bool LB cr o V E sp r g fx R M model K HH Hh Hl Hmat HK0 Hfp Hra Hrok Hsp Htp STK A0 A1 A3 DV EC RO LS HG OO DO OE OV AOE AOV AVE _ EV ES CR Hcont b eq_refl).
  - exact (arm_int LB cr o V E sp r g fx R M model K HH Hh Hl Hmat HK0 Hfp Hra Hrok Hsp Htp STK A0 A1 A3 DV EC RO LS HG OO DO OE OV AOE AOV AVE _ EV ES CR Hcont
             16 GST.R_I64 PMFC.PC_FROM_INT_I64 (proj1 (proj2 EV)) I (ra_ok_lit GST.R_I64 eq_refl) (GSS.s_g_i64 FPM) (GSS.s_g_ri64 FPM) FROMI).
  - exact (arm_int LB cr o V E sp r g fx R M model K HH Hh Hl Hmat HK0 Hfp Hra Hrok Hsp Htp STK A0 A1 A3 DV EC RO LS HG OO DO OE OV AOE AOV AVE _ EV ES CR Hcont
             32 GST.R_U64 PMFC.PC_FROM_INT_U64 (proj1 (proj2 EV)) I (ra_ok_lit GST.R_U64 eq_refl) (GSS.s_g_u64 FPM) (GSS.s_g_ru64 FPM) FROMU).
  - exact (arm_dbl LB cr o V E sp r g fx R M model K HH Hh Hl Hmat HK0 Hfp Hra Hrok Hsp Htp STK A0 A1 A3 DV EC RO LS HG OO DO OE OV AOE AOV AVE _ EV ES CR Hcont x eq_refl).
  - exact (arm_text LB cr o V E sp r g fx R M model K HH Hh Hl Hmat HK0 Hfp Hra Hrok Hsp Htp STK A0 A1 A3 DV EC RO LS HG OO DO OE OV AOE AOV AVE _ EV ES CR Hcont
             p n (or_introl eq_refl) (GSS.s_g_str FPM) (GSS.s_g_rstr FPM)).
  - exact (arm_text LB cr o V E sp r g fx R M model K HH Hh Hl Hmat HK0 Hfp Hra Hrok Hsp Htp STK A0 A1 A3 DV EC RO LS HG OO DO OE OV AOE AOV AVE _ EV ES CR Hcont
             p n (or_intror eq_refl) (GSS.s_g_key FPM) (GSS.s_g_rkey FPM)).
  - exact (arm_cont LB cr o V E sp r g fx R M model K HH Hh Hl Hmat HK0 Hfp Hra Hrok Hsp Htp STK A0 A1 A3 DV EC RO LS HG OO DO OE OV AOE AOV AVE _ EV ES CR Hcont
             256 (proj2 EV) (fun X => X) (GSS.s_g_bobj FPM) (GSS.s_g_rbobj FPM)).
  - exact (arm_cont LB cr o V E sp r g fx R M model K HH Hh Hl Hmat HK0 Hfp Hra Hrok Hsp Htp STK A0 A1 A3 DV EC RO LS HG OO DO OE OV AOE AOV AVE _ EV ES CR Hcont
             512 (proj2 EV) (fun X => X) (GSS.s_g_eobj FPM) (GSS.s_g_reobj FPM)).
  - exact (arm_cont LB cr o V E sp r g fx R M model K HH Hh Hl Hmat HK0 Hfp Hra Hrok Hsp Htp STK A0 A1 A3 DV EC RO LS HG OO DO OE OV AOE AOV AVE _ EV ES CR Hcont
             1024 (proj2 EV) (fun X => X) (GSS.s_g_barr FPM) (GSS.s_g_rbarr FPM)).
  - exact (arm_cont LB cr o V E sp r g fx R M model K HH Hh Hl Hmat HK0 Hfp Hra Hrok Hsp Htp STK A0 A1 A3 DV EC RO LS HG OO DO OE OV AOE AOV AVE _ EV ES CR Hcont
             2048 (proj2 EV) (fun X => X) (GSS.s_g_earr FPM) (GSS.s_g_rearr FPM)).
Qed.
End H.
End GTS.
