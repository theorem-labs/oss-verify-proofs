From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoEntryInv DiscoEntryShapes DiscoArm3 DiscoEntSeatStmt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoRo DiscoEntBodyStmt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require McConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require AE2k.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import JtokIs JsonScalar.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require ReacBoxName.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_table_c reac_disco_table_age_c reac_disco_table_json_c disco_json_text disco_json_reader_model disco_json_lemmas
slot_ser_defs slot_ser_pure slot_ser_tokb disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SnprintfDefR.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition a3f_fmt_mac : list Z :=
  [37; 48; 50; 120; 58; 37; 48; 50; 120; 58; 37; 48; 50; 120; 58; 37; 48; 50; 120; 58; 37; 48; 50; 120; 58;
   37; 48; 50; 120].
Definition a3f_fmt_wid : list Z := [37; 100; 120; 37; 100].
Definition a3f_fmt_age : list Z := [37; 108; 108; 117].
Definition a3f_KDV : Z := 4835703278458516699.

Lemma a3f_count : forall (T : list byte) now count os,
  length T = 400%nat -> disco_table_c.table_ok T -> 0 <= now < 2 ^ 64 ->
  disco_json_reader_model.json_read (a3_text T now) 9 = Some (count, os) ->
  count = disco_table_c.n_of T /\ 0 <= count <= 8 /\ length os = Z.to_nat count /\
  Forall (fun o => length o = 6%nat) os /\
  Forall (Forall (slot_ser_tokb.tok_inb (a3_text T now))) os /\
  Forall (fun c => 33 <= c <= 255) (a3_text T now) /\ (length (a3_text T now) <= 969)%nat.
Proof.
  intros T now count os LT TOK Hnow JR.
  pose proof (slot_ser_pure.ser_tj_ok T LT TOK) as [TOK' WF].
  destruct (disco_json_lemmas.F1_2_json_read_table reac_disco_table_json_c.box_tok
              (reac_disco_table_json_c.tj_entries T) now slot_ser_pure.ser_tok_ok TOK' WF Hnow) as (os' & JR' & F2).
  change (disco_json_text.table_json_text reac_disco_table_json_c.box_tok (reac_disco_table_json_c.tj_entries T) now)
    with (a3_text T now) in JR'.
  rewrite JR in JR'. injection JR' as Ec Eo. subst os'.
  pose proof (slot_ser_pure.ser_tj_len T) as LE. pose proof TOK as (T1 & _). unfold disco_table_c.tbl_T1 in T1.
  pose proof (Forall2_length F2) as LF.
  split; [rewrite Ec, LE; lia|]. split; [rewrite Ec; destruct TOK' as (TL & _); lia|].
  split; [rewrite <- LF, Ec; lia|]. split.
  { clear -F2. induction F2 as [|e o E O V F IH]; constructor; [|exact IH].
    apply (f_equal (@length _)) in V. unfold disco_json_lemmas.obj_view in V. rewrite length_map in V. exact V. }
  split; [exact (slot_ser_tokb.json_read_inb _ _ _ _ JR)|]. split.
  { exact (slot_ser_pure.ser_text_g33 reac_disco_table_json_c.box_tok (reac_disco_table_json_c.tj_entries T) now
             slot_ser_pure.ser_tok_ok WF Hnow). }
  exact (disco_json_lemmas.C7_text_bound reac_disco_table_json_c.box_tok (reac_disco_table_json_c.tj_entries T) now
           slot_ser_pure.ser_tok_ok TOK' WF Hnow).
Qed.

Lemma a3f_tj_nth : forall T k, 0 <= k < disco_table_c.n_of T ->
  nth_error (reac_disco_table_json_c.tj_entries T) (Z.to_nat k) = Some (reac_disco_table_json_c.tj_entry T k).
Proof.
  intros T k Hk. unfold reac_disco_table_json_c.tj_entries. rewrite nth_error_map.
  rewrite (nth_error_nth' (seq 0 (Z.to_nat (disco_table_c.n_of T))) 0%nat) by (rewrite length_seq; lia).
  rewrite seq_nth by lia. cbn [option_map]. f_equal. f_equal. lia.
Qed.

Lemma a3f_obj : forall (T : list byte) now count os k,
  length T = 400%nat -> disco_table_c.table_ok T -> 0 <= now < 2 ^ 64 ->
  disco_json_reader_model.json_read (a3_text T now) 9 = Some (count, os) -> 0 <= k < count ->
  let X := a3_text T now in let o := nth (Z.to_nat k) os [] in let e := reac_disco_table_json_c.tj_entry T k in
  (forall j, 0 <= j < count ->
     disco_json_reader_model.jtok_is X (nth 0 o disco_json_reader_model.tok_none) 1
       (disco_json_text.mac_text (disco_json_text.e_mac (reac_disco_table_json_c.tj_entry T j))) = (j =? k)) /\
  disco_json_reader_model.jtok_is X (nth 1 o disco_json_reader_model.tok_none) 1
    (disco_json_text.rolename (disco_json_text.e_role e)) = true /\
  disco_json_reader_model.jtok_is X (nth 2 o disco_json_reader_model.tok_none) 1
    (fst (disco_json_text.model_of reac_disco_table_json_c.box_tok e)) = true /\
  disco_json_reader_model.jtok_is X (nth 3 o disco_json_reader_model.tok_none) 1
    (snd (disco_json_text.model_of reac_disco_table_json_c.box_tok e)) = true /\
  disco_json_reader_model.jtok_is X (nth 4 o disco_json_reader_model.tok_none) 3 (disco_json_text.owned_text e) = true /\
  disco_json_reader_model.jtok_is X (nth 5 o disco_json_reader_model.tok_none) 2
    (disco_json_text.dec (disco_json_text.age_of now (disco_json_text.e_last_seen e))) = true.
Proof.
  intros T now count os k LT TOK Hnow JR Hk X o e.
  destruct (a3f_count T now count os LT TOK Hnow JR) as (Ec & Hc & Los & _).
  pose proof (slot_ser_pure.ser_tj_ok T LT TOK) as [TOK' WF].
  assert (JR' : disco_json_reader_model.json_read
                  (disco_json_text.table_json_text reac_disco_table_json_c.box_tok
                     (reac_disco_table_json_c.tj_entries T) now) 9 =
                Some (Z.of_nat (length (reac_disco_table_json_c.tj_entries T)), os)).
  { rewrite slot_ser_pure.ser_tj_len, Z2Nat.id by lia. rewrite <- Ec. exact JR. }
  assert (Eo : nth_error os (Z.to_nat k) = Some o) by (apply nth_error_nth'; lia).
  pose proof (a3f_tj_nth T k ltac:(lia)) as Ek.
  destruct (disco_json_lemmas.F1_3_serialise_finds reac_disco_table_json_c.box_tok (reac_disco_table_json_c.tj_entries T)
              now os slot_ser_pure.ser_tok_ok TOK' WF Hnow JR' (Z.to_nat k) _ _ Eo Ek)
    as (M & R & Mo & Wd & O & A).
  split; [|exact (conj R (conj Mo (conj Wd (conj O A))))].
  intros j Hj. specialize (M (Z.to_nat j) (reac_disco_table_json_c.tj_entry T j) (a3f_tj_nth T j ltac:(lia))).
  destruct (Z.eqb_spec j k) as [->|N]; [apply M; reflexivity|].
  apply not_true_is_false. intros E. apply M in E. lia.
Qed.

Lemma a3f_quot : forall x, 0 <= x < 2 ^ 64 -> x * a3f_KDV / 2 ^ 64 / 2 ^ 18 = x / 1000000.
Proof.
  intros x Hx. rewrite Z.div_div by lia. unfold a3f_KDV.
  pose proof (Z.div_mod x 1000000 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 1000000 ltac:(lia)) as M.
  set (q := x / 1000000) in *. set (r := x mod 1000000) in *.
  symmetry. apply Z.div_unique with (r := x * 4835703278458516699 - q * 4835703278458516698824704); [left|ring].
  split; lia.
Qed.

Definition PH_OFF : Z := 0x1d6c.
Definition PF_OFF : Z := 0x1da8.
Definition PFX_OFF : Z := 0x1f00.
Definition MD_OFF : Z := 0x20c8.

Definition a3f_used (p : Z) : list Z :=
  concat (map (fun k => [if Z.of_nat k <? p then 1 else 0; 0; 0; 0]) (seq 0 8)).

Definition live_md (o : dobj) : bool :=
  match o with OO | OUSED | ONM | OTOK | ODISP | OWID | OOUR | OT | OG | OLOCK => true | _ => false end.
Definition dsh_md : Z -> Z := dsh live_md.

Definition a3f_ent (T : list byte) (p : Z) : disco_json_text.entry := reac_disco_table_json_c.tj_entry T p.
Definition a3f_model (T : list byte) (p : Z) : list Z * list Z :=
  disco_json_text.model_of reac_disco_table_json_c.box_tok (a3f_ent T p).

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DLAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PAL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMSET : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA DS___asan_memset).
Hypothesis ASNPRINTF : forall fq : YK11.FPState,
  SnprintfDefR.asnprintf_realizesR (fx := fq) SEGS B pa_relro_lo pa_relro_hi AE2k.FF_got_canary AE2k.FF_canary YImgTop.IMG_LO YImgTop.IMG_TOP
    disco_fmt_lo disco_fmt_hi snp_cr (SIGMA DS___interceptor_trampoline_snprintf).
Hypothesis TJTOK : tjtok_is_spec B.
Hypothesis TBOX : ReacBoxName.treac_box_name_spec B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis DRO : disco_ro_unowned B.
Hypothesis GM : globs_marked SEGS B disco_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Hypothesis DCRO : dimg_consts_of_ro_stmt B.
Hypothesis SNPRO : forall a, Exists (in_zr a) snp_cr -> in_roP SEGS pa_relro_lo pa_relro_hi a.
Hypothesis SNPUN : forall a, Exists (in_zr a) snp_cr ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis MCRO : forall a, McConsts.MC_CONSTS_LO <= a < McConsts.MC_CONSTS_HI -> in_roP SEGS pa_relro_lo pa_relro_hi a.
Hypothesis MCUN : forall a, McConsts.MC_CONSTS_LO <= a < McConsts.MC_CONSTS_HI ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).

Definition a3f_st (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
  (os : list disco_json_reader_model.jobj) (vpad : list byte) (pc : Z) (shf : Z -> Z)
  (R : bvmap 5 word -> Prop) (Y : world SEGS -> (word -> option byte) -> Prop) : world SEGS -> config -> Prop :=
  fun W3 c3 => a3_from B MT XM_LIB RLO RHI tfib_K cx h i n now op T0 W0 c0 W3 /\
    d_arm_at_pf B MT XM_LIB RLO RHI tfib_K cx pc h i n now (a3_xb buf op) shf
      (fun regs => getr regs 26 = w64 buf /\ R regs)
      (fun W m => d_sp1 cx i n now W m /\ a3_tab cx now T0 T1 W m /\ a3_buf op T1 now buf W m /\
         disco_json_reader_model.json_read (a3_text T1 now) 9 = Some (count, os) /\ length vpad = 4%nat /\
         garr8 SEGS (rd W m) (d_obj cx OO)
           (map (fun b : byte => bv_unsigned b) (slot_ser_defs.objs_bytes buf vpad os)) /\
         Y W m) W3 c3.

Definition a3f_slots (cx : dcx) (p count : Z) (W : world SEGS) (m : word -> option byte) : Prop :=
  0 <= p < count /\ val_mem SEGS (rd W m) (d_A cx + 368) 8 p /\ val_mem SEGS (rd W m) (d_A cx + 336) 8 count.

Definition f_ph (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
  (os : list disco_json_reader_model.jobj) (vpad : list byte) (p : Z) : world SEGS -> config -> Prop :=
  a3f_st cx h i n now op W0 c0 T0 T1 buf count os vpad PH_OFF dsh_ser2
    (fun regs => getr regs 22 = w64 (d_obj cx OT))
    (fun W m => a3f_slots cx p count W m /\ garr8 SEGS (rd W m) (d_obj cx OUSED) (a3f_used p)).

Definition f_pf (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
  (os : list disco_json_reader_model.jobj) (vpad : list byte) (p j : Z) : world SEGS -> config -> Prop :=
  a3f_st cx h i n now op W0 c0 T0 T1 buf count os vpad PF_OFF dsh_ser2
    (fun regs => getr regs 11 = w64 (shadow_addr (d_FB cx)) /\
       getr regs 21 = w64 (shadow_addr (d_FB cx) + 270 + 6 * (j - 1)) /\
       getr regs 22 = w64 (d_obj cx OT + 48 * (j - 1)) /\ getr regs 23 = w64 (j - 1) /\ getr regs 24 = w64 j /\
       getr regs 27 = w64 (d_obj cx OT + 48 * (j - 1) + 2))
    (fun W m => a3f_slots cx p count W m /\ 1 <= j <= p + 1 /\
       val_mem SEGS (rd W m) (d_A cx + 392) 8 (d_obj cx OO + 144 * p) /\
       val_mem SEGS (rd W m) (d_A cx + 408) 8 (2 ^ 64 - 1) /\
       garr8 SEGS (rd W m) (d_obj cx OUSED) (a3f_used p)).

Definition f_pfx (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
  (os : list disco_json_reader_model.jobj) (vpad : list byte) (p : Z) : world SEGS -> config -> Prop :=
  a3f_st cx h i n now op W0 c0 T0 T1 buf count os vpad PFX_OFF dsh_ser2
    (fun regs => getr regs 14 = w64 (d_obj cx OT))
    (fun W m => a3f_slots cx p count W m /\
       val_mem SEGS (rd W m) (d_A cx + 392) 8 (d_obj cx OO + 144 * p) /\
       val_mem SEGS (rd W m) (d_A cx + 408) 8 p /\
       garr8 SEGS (rd W m) (d_obj cx OUSED) (a3f_used p)).

Definition a3f_mstr (cx : dcx) (W : world SEGS) (m : word -> option byte) (mp : Z) (s : list Z) : Prop :=
  (mp = VAL (A_OBJ 11) /\ s = disco_json_text.s_unknown) \/
  (mp = d_obj cx OTOK /\ garr8 SEGS (rd W m) mp (s ++ [0])).

Definition f_md (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
  (os : list disco_json_reader_model.jobj) (vpad : list byte) (p mp : Z) : world SEGS -> config -> Prop :=
  a3f_st cx h i n now op W0 c0 T0 T1 buf count os vpad MD_OFF dsh_md
    (fun regs => getr regs 22 = w64 mp /\ getr regs 24 = w64 (d_obj cx OT + 48 * p))
    (fun W m => a3f_slots cx p count W m /\
       val_mem SEGS (rd W m) (d_A cx + 392) 8 (d_obj cx OO + 144 * p) /\
       val_mem SEGS (rd W m) (d_A cx + 408) 8 p /\
       garr8 SEGS (rd W m) (d_obj cx OUSED) (a3f_used (p + 1)) /\
       garr8 SEGS (rd W m) (d_obj cx OWID) (snd (a3f_model T1 p) ++ [0]) /\
       a3f_mstr cx W m mp (fst (a3f_model T1 p))).

Definition seg_e0_spec : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
         (os : list disco_json_reader_model.jobj) (vpad : list byte) (W : world SEGS) (c : config),
  r12_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad W c ->
  SRr SEGS W c (fun W' c' => r14_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf W' c' \/
    f_ph cx h i n now op W0 c0 T0 T1 buf count os vpad 0 W' c').

Definition seg_ph_spec : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
         (os : list disco_json_reader_model.jobj) (vpad : list byte) (p : Z) (W : world SEGS) (c : config),
  f_ph cx h i n now op W0 c0 T0 T1 buf count os vpad p W c ->
  SRr SEGS W c (f_pf cx h i n now op W0 c0 T0 T1 buf count os vpad p 1).

Definition seg_pf_spec : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
         (os : list disco_json_reader_model.jobj) (vpad : list byte) (p j : Z) (W : world SEGS) (c : config),
  f_pf cx h i n now op W0 c0 T0 T1 buf count os vpad p j W c ->
  SRr SEGS W c (fun W' c' => (j <= p /\ f_pf cx h i n now op W0 c0 T0 T1 buf count os vpad p (j + 1) W' c') \/
    f_pfx cx h i n now op W0 c0 T0 T1 buf count os vpad p W' c').

Definition seg_pfx_spec : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
         (os : list disco_json_reader_model.jobj) (vpad : list byte) (p : Z) (W : world SEGS) (c : config),
  f_pfx cx h i n now op W0 c0 T0 T1 buf count os vpad p W c ->
  SRr SEGS W c (fun W' c' => exists mp, f_md cx h i n now op W0 c0 T0 T1 buf count os vpad p mp W' c').

Definition seg_md_spec : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
         (os : list disco_json_reader_model.jobj) (vpad : list byte) (p mp : Z) (W : world SEGS) (c : config),
  f_md cx h i n now op W0 c0 T0 T1 buf count os vpad p mp W c ->
  SRr SEGS W c (fun W' c' => (p + 1 < count /\ f_ph cx h i n now op W0 c0 T0 T1 buf count os vpad (p + 1) W' c') \/
    r14_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf W' c').

Lemma f_ph_p : forall cx h i n now op W0 c0 T0 T1 buf count os vpad p W c,
  f_ph cx h i n now op W0 c0 T0 T1 buf count os vpad p W c -> 0 <= p < count.
Proof.
  intros cx h i n now op W0 c0 T0 T1 buf count os vpad p W c (_ & Hd).
  destruct Hd as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & _ & _ & _ & _ & _ & _ & _ & _ & _ & P).
  destruct P as (_ & _ & _ & _ & _ & Y & _). destruct Y as (_ & _ & _ & _ & _ & _ & (Hp & _) & _). exact Hp.
Qed.

Lemma f_pf_pj : forall cx h i n now op W0 c0 T0 T1 buf count os vpad p j W c,
  f_pf cx h i n now op W0 c0 T0 T1 buf count os vpad p j W c -> 0 <= p < count /\ 1 <= j <= p + 1.
Proof.
  intros cx h i n now op W0 c0 T0 T1 buf count os vpad p j W c (_ & Hd).
  destruct Hd as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & _ & _ & _ & _ & _ & _ & _ & _ & _ & P).
  destruct P as (_ & _ & _ & _ & _ & Y & _). destruct Y as (_ & _ & _ & _ & _ & _ & (Hp & _) & Hj & _).
  exact (conj Hp Hj).
Qed.

Definition seg_pf_pj_spec (p j : Z) : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
         (os : list disco_json_reader_model.jobj) (vpad : list byte) (W : world SEGS) (c : config),
  f_pf cx h i n now op W0 c0 T0 T1 buf count os vpad p j W c ->
  SRr SEGS W c (fun W' c' => (j <= p /\ f_pf cx h i n now op W0 c0 T0 T1 buf count os vpad p (j + 1) W' c') \/
    f_pfx cx h i n now op W0 c0 T0 T1 buf count os vpad p W' c').

Definition seg_pfx_p_spec (p : Z) : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
         (os : list disco_json_reader_model.jobj) (vpad : list byte) (W : world SEGS) (c : config),
  f_pfx cx h i n now op W0 c0 T0 T1 buf count os vpad p W c ->
  SRr SEGS W c (fun W' c' => exists mp, f_md cx h i n now op W0 c0 T0 T1 buf count os vpad p mp W' c').

Definition seg_md_p_spec (p : Z) : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
         (os : list disco_json_reader_model.jobj) (vpad : list byte) (mp : Z) (W : world SEGS) (c : config),
  f_md cx h i n now op W0 c0 T0 T1 buf count os vpad p mp W c ->
  SRr SEGS W c (fun W' c' => (p + 1 < count /\ f_ph cx h i n now op W0 c0 T0 T1 buf count os vpad (p + 1) W' c') \/
    r14_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf W' c').

Lemma a3f_st_c8 : forall cx h i n now op W0 c0 T0 T1 buf count os vpad pc shf R Y W c,
  a3f_st cx h i n now op W0 c0 T0 T1 buf count os vpad pc shf R Y W c -> 0 <= count <= 8 /\ exists m, Y W m.
Proof.
  intros cx h i n now op W0 c0 T0 T1 buf count os vpad pc shf R Y W c (_ & Hd).
  destruct Hd as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & _ & _ & _ & _ & _ & _ & _ & _ & _ & P).
  destruct P as (_ & _ & Hnow & _ & _ & Yx & _).
  destruct Yx as (_ & ((removed & _ & Hpost) & _) & _ & JR & _ & _ & HY).
  destruct Hpost as (LT & _ & _ & _ & _ & _ & TOK & _).
  destruct (a3f_count T1 now count os LT TOK Hnow JR) as (_ & Hc8 & _).
  split; [exact Hc8|]. exists mem3. exact HY.
Qed.

Lemma seg_pf_of_cases : (forall p j, 0 <= p < 8 -> 1 <= j <= p + 1 -> seg_pf_pj_spec p j) -> seg_pf_spec.
Proof.
  intros H cx h i n now op W0 c0 T0 T1 buf count os vpad p j W c Hs.
  destruct (a3f_st_c8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hs) as (Hc8 & m & (Hp & _) & Hj & _).
  exact (H p j ltac:(lia) Hj cx h i n now op W0 c0 T0 T1 buf count os vpad W c Hs).
Qed.

Lemma seg_pfx_of_cases : (forall p, 0 <= p < 8 -> seg_pfx_p_spec p) -> seg_pfx_spec.
Proof.
  intros H cx h i n now op W0 c0 T0 T1 buf count os vpad p W c Hs.
  destruct (a3f_st_c8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hs) as (Hc8 & m & (Hp & _) & _).
  exact (H p ltac:(lia) cx h i n now op W0 c0 T0 T1 buf count os vpad W c Hs).
Qed.

Lemma seg_md_of_cases : (forall p, 0 <= p < 8 -> seg_md_p_spec p) -> seg_md_spec.
Proof.
  intros H cx h i n now op W0 c0 T0 T1 buf count os vpad p mp W c Hs.
  destruct (a3f_st_c8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hs) as (Hc8 & m & (Hp & _) & _).
  exact (H p ltac:(lia) cx h i n now op W0 c0 T0 T1 buf count os vpad mp W c Hs).
Qed.

Definition d_rLs (cx : dcx) (so : Z) (regs : bvmap 5 word) : Prop :=
  spZ regs = d_A cx + so /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  getr regs 8 = w64 (d_S cx) /\ getr regs 9 = w64 (d_A cx) /\ getr regs 18 = w64 SHADOW_OFF /\
  getr regs 20 = w64 WS_MASK /\ getr regs 25 = w64 32.

Definition a3f_stg (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
  (os : list disco_json_reader_model.jobj) (vpad : list byte) (pc so : Z) (shf : Z -> Z)
  (R : bvmap 5 word -> Prop) (Y : world SEGS -> (word -> option byte) -> Prop) : world SEGS -> config -> Prop :=
  fun W3 c3 => a3_from B MT XM_LIB RLO RHI tfib_K cx h i n now op T0 W0 c0 W3 /\
    d_at B MT XM_LIB RLO RHI tfib_K cx pc (EV_HEAD i + 1) (ACC_HEAD MT i + mo_malloc MT REC_MAX)
      (fun regs ly3 S3 W3 mem3 md3 =>
        0 <= i < MAX_OPS /\ 0 <= n /\ 0 <= now < 2 ^ 64 /\
        d_rLs cx so regs /\ getr regs 26 = w64 buf /\ R regs /\
        (d_sp1 cx i n now W3 mem3 /\ a3_tab cx now T0 T1 W3 mem3 /\ a3_buf op T1 now buf W3 mem3 /\
         disco_json_reader_model.json_read (a3_text T1 now) 9 = Some (count, os) /\ length vpad = 4%nat /\
         garr8 SEGS (rd W3 mem3) (d_obj cx OO)
           (map (fun b : byte => bv_unsigned b) (slot_ser_defs.objs_bytes buf vpad os)) /\
         Y W3 mem3) /\
        d_sp0 cx i now W3 mem3 /\ d_body B cx h n (a3_xb buf op) shf ly3 S3 W3 mem3) W3 c3.

Definition R1_OFF : Z := 0x1fac.
Definition BNR_OFF : Z := 0x2090.
Definition MO_OFF : Z := 0x2134.
Definition a3f_wid0 : list Z := [48; 120; 48; 0].
Definition a3f_fam (T : list byte) (p : Z) : Z := disco_table_c.u_at T (48 * p + 15) 1.
Definition a3f_bnret (T : list byte) (p : Z) : Z :=
  disco_box_name_model.bn_ret (a3f_fam T p) [] (disco_table_c.din_of T p) (disco_table_c.dout_of T p).

Definition a3f_pyk (cx : dcx) (p count : Z) (W : world SEGS) (m : word -> option byte) : Prop :=
  a3f_slots cx p count W m /\
  val_mem SEGS (rd W m) (d_A cx + 392) 8 (d_obj cx OO + 144 * p) /\
  val_mem SEGS (rd W m) (d_A cx + 408) 8 p /\
  garr8 SEGS (rd W m) (d_obj cx OUSED) (a3f_used (p + 1)).

Definition f_r1 (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
  (os : list disco_json_reader_model.jobj) (vpad : list byte) (p : Z) : world SEGS -> config -> Prop :=
  a3f_st cx h i n now op W0 c0 T0 T1 buf count os vpad R1_OFF dsh_ser2
    (fun regs => getr regs 24 = w64 (d_obj cx OT + 48 * p))
    (fun W m => a3f_pyk cx p count W m).

Definition a3f_bnregs (cx : dcx) (T1 : list byte) (p : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 19 = w64 (d_obj cx OT + 48 * p + 14) /\
  getr regs 21 = w64 (shadow_addr (d_obj cx OT + 48 * p + 13)) /\
  getr regs 22 = w64 (VAL (A_OBJ 11)) /\
  getr regs 23 = w64 (d_obj cx OT + 48 * p + 13) /\
  getr regs 24 = w64 (d_obj cx OT + 48 * p) /\
  getr regs 27 = w64 (shadow_addr (d_obj cx OT + 48 * p + 14)).

Definition f_bn (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
  (os : list disco_json_reader_model.jobj) (vpad : list byte) (p : Z) : world SEGS -> config -> Prop :=
  a3f_stg cx h i n now op W0 c0 T0 T1 buf count os vpad AF_reac_box_name (-16) dsh_md
    (fun regs => getr regs 1 = w64 (BASE + BNR_OFF) /\ a3f_bnregs cx T1 p regs /\
       getr regs 10 = w64 (a3f_fam T1 p) /\ getr regs 11 = w64 0 /\
       getr regs 12 = w64 (disco_table_c.din_of T1 p) /\ getr regs 13 = w64 (disco_table_c.dout_of T1 p) /\
       getr regs 14 = w64 (d_obj cx ONM) /\ getr regs 15 = w64 24 /\
       getr regs 16 = w64 (d_obj cx OTOK) /\ getr regs 17 = w64 24)
    (fun W m => a3f_pyk cx p count W m /\ disco_table_c.hd_of T1 p <> 0 /\
       val_mem SEGS (rd W m) (d_A cx - 16) 8 (d_obj cx ODISP) /\ val_mem SEGS (rd W m) (d_A cx - 8) 8 48 /\
       garr8 SEGS (rd W m) (d_obj cx OWID) a3f_wid0).

Definition f_bnr (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
  (os : list disco_json_reader_model.jobj) (vpad : list byte) (p : Z) : world SEGS -> config -> Prop :=
  a3f_stg cx h i n now op W0 c0 T0 T1 buf count os vpad BNR_OFF (-16) dsh_md
    (fun regs => a3f_bnregs cx T1 p regs /\
       getr regs 10 = w64 (if a3f_bnret T1 p =? 0 then 0 else -1))
    (fun W m => a3f_pyk cx p count W m /\ disco_table_c.hd_of T1 p <> 0 /\
       garr8 SEGS (rd W m) (d_obj cx OWID) a3f_wid0 /\
       (a3f_bnret T1 p = 0 ->
          garr8 SEGS (rd W m) (d_obj cx OTOK)
            (disco_box_name_model.bn_TK
               (disco_box_name_model.bn_NM (a3f_fam T1 p) [] (disco_table_c.din_of T1 p) (disco_table_c.dout_of T1 p))
             ++ [0]))).

Definition f_mo (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
  (os : list disco_json_reader_model.jobj) (vpad : list byte) (p : Z) : world SEGS -> config -> Prop :=
  a3f_st cx h i n now op W0 c0 T0 T1 buf count os vpad MO_OFF dsh_md
    (fun regs => getr regs 21 = w64 (d_obj cx OO + 144 * p) /\ getr regs 24 = w64 (d_obj cx OT + 48 * p))
    (fun W m => a3f_pyk cx p count W m).

Definition seg_pfa_p_spec (p : Z) : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
         (os : list disco_json_reader_model.jobj) (vpad : list byte) (W : world SEGS) (c : config),
  f_pfx cx h i n now op W0 c0 T0 T1 buf count os vpad p W c ->
  SRr SEGS W c (f_r1 cx h i n now op W0 c0 T0 T1 buf count os vpad p).

Definition seg_pfb_p_spec (p : Z) : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
         (os : list disco_json_reader_model.jobj) (vpad : list byte) (W : world SEGS) (c : config),
  f_r1 cx h i n now op W0 c0 T0 T1 buf count os vpad p W c ->
  SRr SEGS W c (fun W' c' => f_md cx h i n now op W0 c0 T0 T1 buf count os vpad p (VAL (A_OBJ 11)) W' c' \/
    f_bn cx h i n now op W0 c0 T0 T1 buf count os vpad p W' c').

Definition seg_pfc_p_spec (p : Z) : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
         (os : list disco_json_reader_model.jobj) (vpad : list byte) (W : world SEGS) (c : config),
  f_bn cx h i n now op W0 c0 T0 T1 buf count os vpad p W c ->
  SRr SEGS W c (f_bnr cx h i n now op W0 c0 T0 T1 buf count os vpad p).

Definition seg_pfd_p_spec (p : Z) : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
         (os : list disco_json_reader_model.jobj) (vpad : list byte) (W : world SEGS) (c : config),
  f_bnr cx h i n now op W0 c0 T0 T1 buf count os vpad p W c ->
  SRr SEGS W c (fun W' c' => exists mp, f_md cx h i n now op W0 c0 T0 T1 buf count os vpad p mp W' c').

Definition seg_mda_p_spec (p : Z) : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
         (os : list disco_json_reader_model.jobj) (vpad : list byte) (mp : Z) (W : world SEGS) (c : config),
  f_md cx h i n now op W0 c0 T0 T1 buf count os vpad p mp W c ->
  SRr SEGS W c (f_mo cx h i n now op W0 c0 T0 T1 buf count os vpad p).

Definition seg_mdb_p_spec (p : Z) : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
         (os : list disco_json_reader_model.jobj) (vpad : list byte) (W : world SEGS) (c : config),
  f_mo cx h i n now op W0 c0 T0 T1 buf count os vpad p W c ->
  SRr SEGS W c (fun W' c' => (p + 1 < count /\ f_ph cx h i n now op W0 c0 T0 T1 buf count os vpad (p + 1) W' c') \/
    r14_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf W' c').

Lemma seg_pfx_p_of_parts : forall p, seg_pfa_p_spec p -> seg_pfb_p_spec p -> seg_pfc_p_spec p -> seg_pfd_p_spec p ->
  seg_pfx_p_spec p.
Proof.
  intros p HA HB HC HD cx h i n now op W0 c0 T0 T1 buf count os vpad W c Hs.
  eapply SRr_bind; [exact (HA cx h i n now op W0 c0 T0 T1 buf count os vpad W c Hs)|].
  intros W1 c1 _ H1.
  eapply SRr_bind; [exact (HB cx h i n now op W0 c0 T0 T1 buf count os vpad W1 c1 H1)|].
  intros W2 c2 _ [H2 | H2]; [apply SRr_ret; exists (VAL (A_OBJ 11)); exact H2|].
  eapply SRr_bind; [exact (HC cx h i n now op W0 c0 T0 T1 buf count os vpad W2 c2 H2)|].
  intros W3 c3 _ H3. exact (HD cx h i n now op W0 c0 T0 T1 buf count os vpad W3 c3 H3).
Qed.

Lemma seg_md_p_of_parts : forall p, seg_mda_p_spec p -> seg_mdb_p_spec p -> seg_md_p_spec p.
Proof.
  intros p HA HB cx h i n now op W0 c0 T0 T1 buf count os vpad mp W c Hs.
  eapply SRr_bind; [exact (HA cx h i n now op W0 c0 T0 T1 buf count os vpad mp W c Hs)|].
  intros W1 c1 _ H1. exact (HB cx h i n now op W0 c0 T0 T1 buf count os vpad W1 c1 H1).
Qed.

Lemma a3f_compose : seg_e0_spec -> seg_ph_spec -> seg_pf_spec -> seg_pfx_spec -> seg_md_spec ->
  a3_field_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
  intros HE0 HPH HPF HPFX HMD cx h i n now op W0 c0 T0 T1 buf count os vpad W c H.
  eapply SRr_bind; [exact (HE0 cx h i n now op W0 c0 T0 T1 buf count os vpad W c H)|].
  intros W1 c1 _ [H1 | H1]; [apply SRr_ret; exact H1|].
  eapply SRr_loopZ with (m := fun p => count - p)
    (P := fun p W c => f_ph cx h i n now op W0 c0 T0 T1 buf count os vpad p W c) (x := 0); [|exact H1].
  intros p W2 c2 H2. pose proof (f_ph_p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2) as Hp.
  eapply SRr_bind; [exact (HPH cx h i n now op W0 c0 T0 T1 buf count os vpad p W2 c2 H2)|].
  intros W3 c3 _ H3.
  eapply SRr_bind.
  { eapply SRr_loopZ with (m := fun j => p + 1 - j)
      (P := fun j W c => f_pf cx h i n now op W0 c0 T0 T1 buf count os vpad p j W c)
      (Q := f_pfx cx h i n now op W0 c0 T0 T1 buf count os vpad p) (x := 1); [|exact H3].
    intros j W4 c4 H4. pose proof (f_pf_pj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H4) as Hj.
    eapply SRr_mono; [exact (HPF cx h i n now op W0 c0 T0 T1 buf count os vpad p j W4 c4 H4)|].
    intros W5 c5 _ [(Hle & H5) | H5].
    - right. exists (j + 1). split; [lia | exact H5].
    - left. exact H5. }
  intros W4 c4 _ H4.
  eapply SRr_bind; [exact (HPFX cx h i n now op W0 c0 T0 T1 buf count os vpad p W4 c4 H4)|].
  intros W5 c5 _ (mp & H5).
  eapply SRr_mono; [exact (HMD cx h i n now op W0 c0 T0 T1 buf count os vpad p mp W5 c5 H5)|].
  intros W6 c6 _ [(Hlt & H6) | H6].
  - right. exists (p + 1). split; [lia | exact H6].
  - left. exact H6.
Qed.

End h.
End f.
End d.
