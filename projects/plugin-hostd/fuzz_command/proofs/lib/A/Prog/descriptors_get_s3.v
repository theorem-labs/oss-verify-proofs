(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of descriptors_get (plugin-hostd/fuzz_command.asan) from the join of
   record()'s arms to the tail jump into answer, after proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v and ACh2.v (a walk
   segment: run, call out by cl_callS, resume) over fuzz_command's listing. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG05 YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c rec_shape_of_c hand_back_c answer_c descriptors_get_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import descriptors_get_s1 RecBLemmas descriptors_get_s2.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaFx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the footprint the statement names (descriptors_get_c.v:90): g_rec, record.spill, and the recorder's blocks *)
Definition dg_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.
(* the default argument "(null)" (.str.47, 0x22480) and the verb "descriptor_get" (.str.19, 0x21f60) *)
Definition dg_null : list byte := bstr "(null)"%string.
Definition dg_verb : list byte := bstr "descriptor_get"%string.

Lemma dg_null_lit : dg_null ++ [Z_to_bv 8 0] = RO_lit_22480.
Proof. vm_compute. reflexivity. Qed.
Lemma dg_null_nz : ~ In (Z_to_bv 8 0) dg_null.
Proof. unfold dg_null. vm_compute. intros H. repeat (destruct H as [H|H]; [discriminate H|]). exact H. Qed.
Lemma dg_verb_lit : dg_verb ++ [Z_to_bv 8 0] = RO_lit_21f60.
Proof. vm_compute. reflexivity. Qed.
Lemma dg_sarg_none : sarg None = dg_null.
Proof. reflexivity. Qed.
Lemma dg_shape : daemon_shape "descriptor_get" = shape_of dg_verb.
Proof. reflexivity. Qed.
Lemma dg_fits : fits (shape_of dg_verb).
Proof. unfold fits. vm_compute. intros H. discriminate H. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

(* the string the walk hands to xstrdup, at the join: uri, a string in a live heap block (descriptors_get_c.v:86-89) *)
Definition dg_str_atJ (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (pu : Z)
  (uri : option (list byte)) : Prop :=
exists x, uri = Some x /\ in_blockA (ablocks B ly S) pu (Z.of_nat (length x) + 1) /\ astr_atR (rdW W mem) pu x /\
  Z.of_nat (length x) + 1 <= LMAX + 1.

(* the recorder at the join: a state Rb (R itself, or R with the spill's arguments freed) whose representation the
   join's memory keeps outside g_rec.ncalls; the blocks F record() freed (the spill's arguments), all of them the
   recorder's *)
Definition dg_model (ly : alayout) (S : astate) (O : list (Z * Z)) (R : rstate) (lyc : alayout) (Sc : astate)
  (rdc : reader) (c : Z) : Prop :=
exists (F blb : list (Z * Z)) (rdb : reader) (Rb : rstate) (Qb : rlay),
  arep_at blb rdb A_G_REC A_REC_SPILL Rb Qb /\
  (forall A, rec_record Rb REC_DESCRIPTORS_GET A = rec_record R REC_DESCRIPTORS_GET A) /\
  (((length (r_calls Rb) < 16)%nat /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls Rb))) \/
   (length (r_calls Rb) = 16%nat /\ c = A_REC_SPILL /\ l_spill Qb = [])) /\
  aval_mem rdc (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls (rec_record Rb REC_DESCRIPTORS_GET [])))) /\
  (forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
     ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> rdc a = rdb a) /\
  (forall pn, In pn (lay_blocks Qb) -> In pn (ablocks B lyc Sc) /\
     forall i, 0 <= i < snd pn -> rdc (fst pn + i) = rdb (fst pn + i)) /\
  (forall pn, In pn (lay_blocks Qb) -> In pn O) /\
  Permutation (ablocks B ly S) (ablocks B lyc Sc ++ F) /\
  (forall pn, In pn F -> In pn O) /\
  (forall pn, In pn O -> In pn (ablocks B lyc Sc) -> In pn (lay_blocks Qb)) /\
  (F <> [] -> (16 <= length (r_calls R))%nat).

(* the statement's post, descriptors_get_c.v:99-118 verbatim *)
Definition dg_post (ly : alayout) (S : astate) (R : rstate) (O : list (Z * Z)) (uri : option (list byte))
  : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists (R' : rstate) (t : list byte) (q : Z) (O' : list (Z * Z)),
 descriptors_get_m R uri = (R', t) /\
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 In (q, Z.of_nat (length t) + 1) (ablocks B ly' S') /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, Z.of_nat (length t) + 1)) /\ ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q t /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O ->
    In pn (ablocks B ly' S') /\ iv_apart (fst pn) (snd pn) q (Z.of_nat (length t) + 1)) /\
 (forall pn, In pn (ablocks B ly' S') ->
    (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, Z.of_nat (length t) + 1)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_DESCRIPTORS_GET R uri /\
 mo_le MT S S' (XM_DESCRIPTORS_GET MT R uri).

(* the walk from the join of record()'s arms (0x8d014) to the return through answer: what the walk from the entry
   hands over at the join (proved by dg_walkJ below; the entry segment, descriptors_get_s4.v, takes it as its one
   interface) *)
Definition dg_walkJ_stmt : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (pu : Z) (uri : option (list byte)) (R : rstate)
  (O : list (Z * Z)) lyc Sc (Wc : world SEGS) (regs1 : bvmap 5 word) memc mdc k c,
afn_pre SEGS B DESCRIPTORS_GET_STK ly S W regs mem md ch ->
(* rounding mode 0 (the statement's pre, descriptors_get_c.v:78): answer's pre at the tail jump *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
0 <= pu < 2 ^ 64 ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
Z.of_nat (length (frames S)) <= 8 ->
st_nev S + EV_DESCRIPTORS_GET R <= EV_MAX -> blocks_bytes S + LIVE_DESCRIPTORS_GET R uri <= LIVE_MAX ->
mo_ok MT S (XM_DESCRIPTORS_GET MT R uri) ->
ajournal SEGS B DESCRIPTORS_GET_STK (spZ regs) (dg_FP O) ly S W mem md [] lyc Sc Wc memc mdc k ->
k <= rec_spill_frees R -> mo_le MT S Sc (rec_spill_frees R * mo_free MT) ->
dg_regs_ok regs regs1 c pu -> dg_frame_ok (rdW Wc memc) (spZ regs) regs -> dg_slot_ok c ->
dg_str_atJ lyc Sc Wc memc pu uri ->
dg_model ly S O R lyc Sc (rdW Wc memc) c ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + DG_J)) memc (seg_rom SEGS)) mdc)
  (apost_baseF SEGS B DESCRIPTORS_GET_STK (dg_FP O) regs ly S W mem md (EV_DESCRIPTORS_GET R) (dg_post ly S R O uri)).

Hypothesis HB : CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis SIGP : cmd_sig_prog.
(* the per-binary facts the statements do not carry yet, with the recorder walks' shared names *)
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
(* the read-only bytes of the image's literals (CmdRo.v:434), which the verb handed to rec_shape_of needs *)
Hypothesis CMD_RO_IN : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI).
(* a live block's word tail is visible (the heap string handed to xstrdup) *)
Hypothesis cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
In (p, n) (ablocks B ly S) -> p <= e < p + n -> atail_vis SEGS W mem e.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.

(* a byte of the slot is one of the program's statics, in the image, outside the runtime's owned statics and the
   errno cell, and in the statement's footprint *)
Lemma dg_slot_facts : forall O c a, dg_slot_ok c -> c <= a < c + CALL_SIZE ->
Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\
~ (as_errno B <= a < as_errno B + 4) /\ inFP (dg_FP O) a.
Proof.
intros O c a Hc Ha. pose proof (dg_in_PG c a Hc Ha) as HP.
rewrite <- (recb_ts_prog_m B HB) in HP.
destruct (prog_static_sep B a (ts_ok B HB) HP) as (Ho & He & _).
split; [exact HP|]. split; [apply cmd_prog_img; rewrite <- (recb_ts_prog_m B HB); exact HP|].
split; [exact Ho|]. split; [exact He|].
destruct Hc as [(H1 & H2 & _) | ->].
- exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity|]. cbn [fst snd].
  unfold A_G_REC, REC_SIZE, OFF_CALLS, OFF_ANSWER, CALL_SIZE in *. lia.
- exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; left; reflexivity|]. cbn [fst snd].
  unfold A_REC_SPILL, SC_SIZE, CALL_SIZE in *. lia.
Qed.

(* the slot's write window satisfies the journal's write rule: a footprint byte of the program's statics *)
Lemma dg_awr_slot : forall E rs STK sp0 O bl0 blc fr0 lyx own c cs,
bv_unsigned (ew E 8) = c -> dg_slot_ok c ->
awr_ok SEGS B E rs STK sp0 (dg_FP O) bl0 blc fr0 lyx own ->
awr_ok SEGS B E (YP09.mkRegion (Some 8%nat) 0 16 0 16 cs :: rs) STK sp0 (dg_FP O) bl0 blc fr0 lyx own.
Proof.
intros E rs STK sp0 O bl0 blc fr0 lyx own c cs Hc Hok H a (r & [<- | Hin] & Ha).
- cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Hc in Ha.
  destruct (dg_slot_facts O c a Hok ltac:(unfold CALL_SIZE; lia)) as (HP & Hi & _ & _ & HF).
  right; right; right; right. left. split; [exact HF|]. split; [exact HP | exact Hi].
- apply H. exists r. auto.
Qed.

(* the shadow entry of the slot holds at every state of the allocator record *)
Lemma dg_shok : forall E ly S (W : world SEGS) mem md c,
AR SEGS B ly S W mem md -> dg_slot_ok c -> ew E 19 = Z_to_bv 64 SB -> ew E 8 = Z_to_bv 64 c ->
sh_ok SEGS dg_Bx dg_SH E (mrestrict (w_H W) mem).
Proof.
intros E ly S W mem md c HAR Hc E19 E8. destruct (dg_slot_bounds c Hc) as [Hcb _].
assert (USB : SB = 0x7fff8000) by reflexivity. assert (HSO : SHADOW_OFF = 0x7fff8000) by reflexivity.
unfold sh_ok, dg_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E dg_Bx 8%nat c CALL_SIZE c 0 CALL_SIZE).
- exact (dg_slot_addressable B HB ly S W mem md c HAR Hc).
- unfold dg_Bx. rewrite (dg_U_atom E 19%nat SB E19) by (rewrite USB; lia). rewrite USB, HSO. reflexivity.
- apply dg_U_atom; [exact E8 | unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia].
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold CALL_SIZE in Hx. rewrite HSO.
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *. lia.
Qed.

Lemma dg_bsum_perm : forall l l', Permutation l l' -> bsum l = bsum l'.
Proof. intros l l' HP. induction HP; unfold bsum in *; cbn [fold_right] in *; lia. Qed.

Lemma dg_bsum_nonneg : forall l, (forall b, In b l -> 0 <= snd b) -> 0 <= bsum l.
Proof.
intros l. induction l as [|b l IH]; intros H; unfold bsum in *; cbn [fold_right] in *; [lia|].
pose proof (H b (or_introl eq_refl)). pose proof (IH (fun b' Hb' => H b' (or_intror Hb'))). lia.
Qed.

(* the slot's 16 bytes kept by a callee whose footprint is empty *)
Lemma dg_region_kept_slot : forall E STK1 sp1 lyc Sc (W : world SEGS) memc mdc ly2 S2 (W2 : world SEGS) mem2 md2 k1 c cs,
ajournal SEGS B STK1 sp1 [] lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
bv_unsigned (ew E 8) = c -> dg_slot_ok c ->
region_kept SEGS E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some 8%nat) 0 16 0 16 cs).
Proof.
intros E STK1 sp1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 c cs HJ1 Hc Hok.
pose proof HJ1 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & G3 & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hc; intros a Ha.
- destruct (dg_slot_facts [] c a Hok ltac:(unfold CALL_SIZE; lia)) as (_ & Hi & Ho & He & _).
  apply (mbyte_of_aview SEGS). apply G3; [exact Hi | exact Ho | exact He |].
  apply fp_spares_closed; [exact sink_closed_nil | exact (inFP_nil a)].
- intros _. apply (cmd_prog_writable ly2 S2 W2 mem2 md2 a HAR2). apply (dg_in_PG c a Hok). unfold CALL_SIZE. lia.
Qed.

(* no read-only byte lies in the statement's footprint: not in the program's statics (cmd_ro_prog_apart), and not
   in a heap block, which holds no image byte *)
Lemma dg_ro_off_fp : forall ly S (W : world SEGS) mem md O,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
forall a, in_roP SEGS RLO RHI a -> ~ inFP (dg_FP O) a.
Proof.
intros ly S W mem md O HAR HO a Hro (r & Hr & Ha). destruct (cmd_ro_prog_apart a Hro) as [Himg Hnp].
destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- apply Hnp. apply recb_grec_in. exact Ha.
- apply Hnp. apply recb_spill_in. exact Ha.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hin). cbn [fst snd] in Ha.
  exact (recb_heap_noimg_m B ly S W mem md p n a HAR (HO (p, n) Hin) Ha Himg).
Qed.

(* the read-only bytes agree with the image at every state the walk reaches *)
Lemma dg_aro_at : forall ly S (W : world SEGS) mem md lyc Sc (Wc : world SEGS) memc mdc O k sp0,
ajournal SEGS B DESCRIPTORS_GET_STK sp0 (dg_FP O) ly S W mem md [] lyc Sc Wc memc mdc k ->
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW Wc memc).
Proof.
intros ly S W mem md lyc Sc Wc memc mdc O k sp0 HJ HAR HO HR.
exact (arodata_ok_journalP (RO := RRO) SEGS RLO RHI RELRO_IMG B _ _ _ _ _ _ _ _ _ _ _ _ _ _ k HJ
  (dg_ro_off_fp ly S W mem md O HAR HO) HR).
Qed.

Lemma dg_not_owned_b : forall a (L : list (Z * Z)),
existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) L = false -> ~ Exists (in_zr a) L.
Proof.
intros a L. induction L as [|r L IH]; intros H HE; [inversion HE|].
cbn [existsb] in H. apply Bool.orb_false_iff in H as [H1 H2].
inversion HE as [? ? Hr | ? ? Hr]; subst.
- unfold in_zr in Hr. apply Bool.andb_false_iff in H1 as [H1 | H1]; [apply Z.leb_gt in H1 | apply Z.ltb_ge in H1]; lia.
- exact (IH H2 Hr).
Qed.

(* the verb "descriptor_get" (0x21f60, 15 bytes with its NUL): an image string outside the runtime's owned statics
   and the errno cell *)
Lemma dg_verb_unowned : forall i, 0 <= i < 15 ->
~ Exists (in_zr (0x21f60 + i)) (as_owned_static B) /\ ~ (as_errno B <= 0x21f60 + i < as_errno B + 4).
Proof.
intros i Hi. rewrite (ts_owned B HB), (ts_errno B HB). split; [|unfold TFIB_ERRNO; lia].
apply dg_not_owned_b.
assert (Hc : forall j, In j [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14] ->
  existsb (fun r => (fst r <=? 0x21f60 + j) && (0x21f60 + j <? fst r + snd r)) Tfib_owned_static = false).
{ intros j Hj. repeat (destruct Hj as [<- | Hj]; [vm_compute; reflexivity|]). destruct Hj. }
apply Hc. cbn [In]. lia.
Qed.

(* the bytes of a live block lie below 2^47 and outside the program's statics *)
Lemma dg_blk_off : forall ly S (W : world SEGS) mem md p n,
AR SEGS B ly S W mem md -> in_blockA (ablocks B ly S) p n ->
forall a, p <= a < p + n -> 4096 <= a < 2 ^ 47 /\ ~ Exists (in_zr a) recb_PG /\
  exists q k, In (q, k) (ablocks B ly S) /\ q <= a < q + k.
Proof.
intros ly S W mem md p n HAR (q & kq & Hin & Hq1 & Hq2) a Ha.
destruct (al_blocks _ _ LAWS ly S W mem md q kq HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hk).
pose proof (req_size_pos kq ltac:(lia)) as [_ Hreq]. pose proof asan_consts as (C1 & _).
assert (Hni : ~ in_img SEGS a) by (apply (recb_heap_noimg_m B ly S W mem md q kq a HAR Hin); lia).
split; [lia|]. split; [intros HP; exact (Hni (cmd_prog_img a HP))|]. exists q, kq. split; [exact Hin | lia].
Qed.


(* a callee with an empty footprint keeps the caller's frame (above its window) and every byte of the program's
   statics: the journal's first and third clauses (descriptors_add_s2.v's da_call_kept) *)
Lemma dg_call_kept : forall STK1 sp1 lyc Sc (Wc : world SEGS) memc mdc ly2 S2 (W2 : world SEGS) mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 [] lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
((sp1 <= a < 2 ^ 64 /\ alloc_ceiling <= a) \/ Exists (in_zr a) recb_PG) ->
rdW W2 mem2 a = rdW Wc memc a.
Proof.
intros STK1 sp1 lyc Sc Wc memc mdc ly2 S2 W2 mem2 md2 k1 a HJ Ha.
destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & K1 & _ & K3 & _).
assert (Hnf : ~ inFP [] a) by (intros (r & Hr & _); destruct Hr).
destruct Ha as [(Ha1 & Ha2) | HP].
- apply K1; [lia | lia | exact Hnf].
- assert (HP' : Exists (in_zr a) (as_prog_static B)) by (rewrite (recb_ts_prog_m B HB); exact HP).
  destruct (prog_static_sep B a (ts_ok B HB) HP') as (H1 & H2 & _).
  apply K3; [exact (cmd_prog_img a HP) | exact H1 | exact H2 |].
  apply fp_spares_closed; [intros (r & Hr & _); destruct Hr | exact Hnf].
Qed.

(* ... and every block live before and after it *)
Lemma dg_call_kept_blk : forall STK1 sp1 lyc Sc (Wc : world SEGS) memc mdc ly2 S2 (W2 : world SEGS) mem2 md2 k1 p n i,
ajournal SEGS B STK1 sp1 [] lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
In (p, n) (ablocks B lyc Sc) -> In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n ->
rdW W2 mem2 (p + i) = rdW Wc memc (p + i).
Proof.
intros STK1 sp1 lyc Sc Wc memc mdc ly2 S2 W2 mem2 md2 k1 p n i HJ H1 H2 Hi.
destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & K2 & _).
exact (K2 p n i H1 H2 Hi (fun H => match H with ex_intro _ r (conj Hr _) => match Hr with end end)).
Qed.

(* an own run of the walk writes only inside its windows, which lie in the program's statics *)
Lemma dg_run_keeps : forall E rs (H : word -> bool) (m m' : word -> option byte),
frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, in_wrange E rs a -> Exists (in_zr a) recb_PG) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Exists (in_zr a) recb_PG -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' Hfr Hw a Ha Hn. apply (aview_eq_of SEGS). apply Hfr.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
intros Hin. exact (Hn (Hw a Hin)).
Qed.

Lemma dg_sig_xstrdup : SIG CS_xstrdup = BASE + AF_xstrdup.
Proof. rewrite (SIGP CS_xstrdup ltac:(vm_compute; repeat first [left; reflexivity | right])). reflexivity. Qed.
Lemma dg_sig_rec_shape_of : SIG CS_rec_shape_of = BASE + AF_rec_shape_of.
Proof. rewrite (SIGP CS_rec_shape_of ltac:(vm_compute; repeat first [left; reflexivity | right])). reflexivity. Qed.
Lemma dg_sig_answer : SIG CS_answer = BASE + AF_answer.
Proof. rewrite (SIGP CS_answer ltac:(vm_compute; repeat first [left; reflexivity | right])). reflexivity. Qed.
Lemma dg_null_val : VAL (A_OBJ 52) = 0x22480.
Proof. rewrite (VOBJS 52%nat) by (vm_compute; lia). vm_compute. reflexivity. Qed.
Lemma dg_null_atom : A_OBJ 52 = 293%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma dg_verb_val : VAL (A_OBJ 76) = 0x21f60.
Proof. rewrite (VOBJS 76%nat) by (vm_compute; lia). vm_compute. reflexivity. Qed.
Lemma dg_verb_atom : A_OBJ 76 = 317%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma dg_abytes_prefix : forall (rd : reader) a l1 l2, abytes_atR rd a (l1 ++ l2) -> abytes_atR rd a l1.
Proof.
intros rd a l1 l2 H i Hi. specialize (H i ltac:(rewrite length_app; lia)).
rewrite app_nth1 in H by exact Hi. exact H.
Qed.

(* the verb "descriptor_get" (RO_lit_21f60), as rec_shape_of reads it (rec_shape_of_c.v:86-89): its 14 bytes, and the
   whole string through astr_argA's read-only arm *)
Lemma dg_verb_arg : forall ly S (W : world SEGS) mem, cmd_ro_ok (rdW W mem) ->
abytes_atR (rdW W mem) 0x21f60 dg_verb /\
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) [] 0x21f60 (Some dg_verb).
Proof.
intros ly S W mem HRO.
assert (HL : abytes_atR (rdW W mem) 0x21f60 RO_lit_21f60).
{ clear - HRO. destruct HRO as [HRO _]. unfold cmd_ro_bytes in HRO.
  repeat match type of HRO with
  | abytes_atR _ 0x21f60 _ /\ _ => exact (proj1 HRO)
  | _ /\ _ => apply proj2 in HRO
  end. }
assert (HI : forall i, 0 <= i < 15 -> in_roP SEGS RLO RHI (0x21f60 + i)).
{ clear - CMD_RO_IN. pose proof CMD_RO_IN as HRI. unfold cmd_ro_in in HRI.
  repeat match type of HRI with
  | (forall i, 0 <= i < _ -> _ (0x21f60 + i)) /\ _ => exact (proj1 HRI)
  | _ /\ _ => apply proj2 in HRI
  end. }
rewrite <- dg_verb_lit in HL.
split; [exact (dg_abytes_prefix _ _ _ _ HL)|].
unfold astr_argA. split; [discriminate|]. split; [split; [exact HL | vm_compute; intros H; repeat (destruct H as [H|H]; [discriminate H|]); exact H]|].
change (Z.of_nat (length dg_verb) + 1) with 15. split; [unfold LMAX; lia|].
right. split; [intros i Hi; split; [exact (HI i Hi) | exact (dg_verb_unowned i Hi)]|].
split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
apply In_of_existsb. vm_compute. reflexivity.
Qed.
(* the live bytes only shrink over frees *)
Lemma dg_bytes_le : forall ly S (W : world SEGS) mem md lyc Sc F,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (ablocks B lyc Sc ++ F) -> blocks_bytes Sc <= blocks_bytes S.
Proof.
intros ly S W mem md lyc Sc F HAR HP.
rewrite (blocks_bytes_bsum B lyc Sc), (blocks_bytes_bsum B ly S), (bsum_perm _ _ HP), bsum_app.
assert (0 <= bsum F); [|lia].
apply dg_bsum_nonneg. intros [p n] Hb. cbn [snd].
assert (Hin : In (p, n) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); apply in_app_iff; right; exact Hb).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn). lia.
Qed.

(* the walk's write windows after the join: the frame (none) and the slot's first 16 bytes *)
Lemma dg_wr_slot : forall E rs c a, bv_unsigned (ew E 8) = c -> dg_slot_ok c ->
Forall (fun r => (YP09.r_base r = Some 2%nat /\ YP09.r_whi r <= YP09.r_wlo r) \/
  (YP09.r_base r = Some 8%nat /\ 0 <= YP09.r_wlo r /\ YP09.r_whi r <= 16)) rs ->
in_wrange E rs a -> Exists (in_zr a) recb_PG.
Proof.
intros E rs c a Hc Hok HF (r & Hr & Ha). rewrite Forall_forall in HF.
destruct (HF r Hr) as [(Hb & Hw) | (Hb & Hw1 & Hw2)]; [lia|].
rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hc in Ha. apply (dg_in_PG c a Hok). unfold CALL_SIZE. lia.
Qed.
Ltac dg_wr_tac :=
  lazymatch goal with |- Forall _ ?rs =>
    tryif is_evar rs then fail 1 "dg_wr_tac: region list is an evar" else
    let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat apply Forall_cons; try apply Forall_nil; cbn [YP09.r_base YP09.r_wlo YP09.r_whi];
  first [left; split; [reflexivity | lia] | right; split; [reflexivity | lia]].

(* an own run after the join writes only the slot's first 16 bytes *)
Lemma dg_run_keeps_out : forall E rs (H : word -> bool) (m m' : word -> option byte) c,
frame_of E rs (mrestrict H m) (mrestrict H m') -> bv_unsigned (ew E 8) = c ->
Forall (fun r => (YP09.r_base r = Some 2%nat /\ YP09.r_whi r <= YP09.r_wlo r) \/
  (YP09.r_base r = Some 8%nat /\ 0 <= YP09.r_wlo r /\ YP09.r_whi r <= 16)) rs ->
forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 16) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' c Hfr Hc HF a Ha Hn. apply (aview_eq_of SEGS). apply Hfr.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
intros (r & Hr & Hw). rewrite Forall_forall in HF. destruct (HF r Hr) as [(Hb & Hw') | (Hb & Hw1 & Hw2)]; [lia|].
rewrite Hb in Hw. cbn [base_val] in Hw. rewrite Hc in Hw. lia.
Qed.

Lemma dg_PG_range : forall a, Exists (in_zr a) recb_PG -> A_G_REC <= a < A_G_QUITTING + 4.
Proof.
intros a HE. apply Exists_exists in HE as ([lo len] & Hr & Hz). unfold in_zr in Hz. cbn [fst snd] in Hz.
unfold recb_PG in Hr. cbn [In] in Hr. unfold A_G_REC, A_REC_SPILL, A_G_QUITTING, REC_SIZE, SC_SIZE in *.
repeat (destruct Hr as [Hr | Hr]; [injection Hr as <- <-; lia|]). destruct Hr.
Qed.

(* the answer the recorder holds: 0, or the start of one of its blocks *)
Lemma dg_old : forall bl (rd : reader) gr sc R Q, arep_at bl rd gr sc R Q ->
exists old, aval_mem rd (gr + OFF_ANSWER) 8 old /\ (old = 0 \/ exists m, In (old, m) (lay_blocks Q)).
Proof.
intros bl rd gr sc R Q (_ & _ & _ & _ & HA & _). unfold aanswer_at in HA.
destruct (r_answer R) as [x|], (l_answer Q) as [[q m]|] eqn:Eq; try contradiction.
- destruct HA as (H1 & _). exists q. split; [exact H1|]. right. exists m.
  unfold lay_blocks. rewrite Eq. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity.
- exists 0. split; [exact HA | left; reflexivity].
Qed.

Lemma dg_rec_record_len : forall R fn A A',
length (r_calls (rec_record R fn A)) = length (r_calls (rec_record R fn A')).
Proof. intros R fn A A'. unfold rec_record. destruct (Nat.ltb _ _); cbn; [rewrite !length_app; reflexivity | reflexivity]. Qed.

(* a live block is apart from a range of image bytes *)
Lemma dg_heap_iv : forall ly S (W : world SEGS) mem md p n lo len,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 < len ->
(forall a, lo <= a < lo + len -> in_img SEGS a) -> iv_apart p n lo len.
Proof.
intros ly S W mem md p n lo len HAR Hin Hlen Himg. unfold iv_apart.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
destruct (Z_le_gt_dec (p + n) lo) as [H|H]; [left; exact H|].
destruct (Z_le_gt_dec (lo + len) p) as [H'|H']; [right; exact H'|]. exfalso.
pose proof (req_size_pos n ltac:(lia)) as Hq.
apply (recb_heap_noimg_m B ly S W mem md p n (Z.max p lo) HAR Hin); [lia | apply Himg; lia].
Qed.

(* the shadow bytes of a range below 2^47 lie above the program's statics *)
Lemma dg_ra_kept : forall (rd rd' : reader) p n,
range_addressable rd SHADOW_OFF p n -> 0 <= p -> p + n <= 2 ^ 47 ->
(forall a, 0x7fff8000 <= a < 2 ^ 64 -> rd' a = rd a) -> range_addressable rd' SHADOW_OFF p n.
Proof.
intros rd rd' p n Hra Hp Hn HK x Hx. destruct (Hra x Hx) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
unfold shadow_of_addr, SHADOW_OFF in *. rewrite HK; [exact Hsv|].
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

(* a g_rec byte is one the walk may write: awr_byte's program-static disjunct *)
Lemma dg_awr_grec : forall STK sp0 O bl0 blc fr0 lyx own a,
A_G_REC <= a < A_G_REC + REC_SIZE -> awr_byte SEGS B STK sp0 (dg_FP O) bl0 blc fr0 lyx own a.
Proof.
intros STK sp0 O bl0 blc fr0 lyx own a Ha. pose proof (recb_grec_in a Ha) as HP.
right; right; right; right. left.
split; [exists (A_G_REC, A_G_REC + REC_SIZE); split; [left; reflexivity | cbn [fst snd]; lia]|].
split; [rewrite (recb_ts_prog_m B HB); exact HP | exact (cmd_prog_img a HP)].
Qed.

(* no byte at or above the allocation ceiling is in the statement's footprint *)
Lemma dg_notFP_high : forall ly S (W : world SEGS) mem md O a,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) -> alloc_ceiling <= a -> ~ inFP (dg_FP O) a.
Proof.
intros ly S W mem md O a HAR HO Ha (r & Hr & Hra). pose proof asan_consts as (C1 & _).
destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Hra; [unfold A_G_REC, REC_SIZE in Hra; lia | unfold A_REC_SPILL, SC_SIZE in Hra; lia|].
unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([b n] & <- & Hin). cbn [fst snd] in Hra.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR (HO _ Hin)) as (_ & _ & Hc & _). lia.
Qed.

Definition dg_pz_dec : forall a b : Z * Z, {a = b} + {a <> b}.
Proof. decide equality; apply Z.eq_dec. Defined.

Lemma dg_pairwise_map : forall {X Y} (R : Y -> Y -> Prop) (f : X -> Y) l,
pairwise R (map f l) -> pairwise (fun a b => R (f a) (f b)) l.
Proof.
intros X Y R f l. induction l as [|x l IH]; cbn [map pairwise]; [tauto|].
intros [Hf Hp]. split; [|exact (IH Hp)]. rewrite Forall_map in Hf. exact Hf.
Qed.

Lemma dg_pairwise_in : forall {X} (R : X -> X -> Prop) l x y, (forall a b, R a b -> R b a) ->
pairwise R l -> List.NoDup l -> In x l -> In y l -> x <> y -> R x y.
Proof.
intros X R l. induction l as [|z l IH]; intros x y Hs Hp Hnd Hx Hy Hne; [destruct Hx|].
cbn [pairwise] in Hp. destruct Hp as [Hf Hp]. rewrite Forall_forall in Hf. inversion Hnd as [|? ? Hz Hnd']; subst.
destruct Hx as [<- | Hx]; destruct Hy as [<- | Hy].
- exfalso. exact (Hne eq_refl).
- exact (Hf y Hy).
- exact (Hs _ _ (Hf x Hx)).
- exact (IH x y Hs Hp Hnd' Hx Hy Hne).
Qed.

(* two live blocks are one block or apart, over their rounded sizes *)
Lemma dg_blocks_apart : forall ly S (W : world SEGS) mem md b1 b2,
AR SEGS B ly S W mem md -> In b1 (ablocks B ly S) -> In b2 (ablocks B ly S) -> b1 <> b2 ->
zdisjoint (fst b1, req_size (snd b1)) (fst b2, req_size (snd b2)).
Proof.
intros ly S W mem md b1 b2 HAR H1 H2 Hne.
pose proof (recb_ablocks_nodup_m B ly S W mem md HAR) as Hnd.
destruct (al_sep _ _ LAWS _ _ _ _ _ HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
apply (dg_pairwise_map zdisjoint (fun b : Z * Z => (fst b, req_size (snd b)))) in Hp.
exact (dg_pairwise_in (fun a b : Z * Z => zdisjoint (fst a, req_size (snd a)) (fst b, req_size (snd b))) _ b1 b2
  ltac:(intros a b Hab; unfold zdisjoint in *; cbn [fst snd] in *; lia) Hp Hnd H1 H2 Hne).
Qed.

(* hence one block per start, and distinct blocks apart over their sizes *)
Lemma dg_blocks_start : forall ly S (W : world SEGS) mem md b1 b2,
AR SEGS B ly S W mem md -> In b1 (ablocks B ly S) -> In b2 (ablocks B ly S) -> fst b1 = fst b2 -> b1 = b2.
Proof.
intros ly S W mem md [p1 n1] [p2 n2] HAR H1 H2 He. cbn [fst] in He.
destruct (dg_pz_dec (p1, n1) (p2, n2)) as [E|Hne]; [exact E|]. exfalso.
pose proof (dg_blocks_apart ly S W mem md _ _ HAR H1 H2 Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p1 n1 HAR H1) as (_ & _ & _ & _ & _ & _ & Hn1).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p2 n2 HAR H2) as (_ & _ & _ & _ & _ & _ & Hn2).
pose proof (req_size_pos n1 ltac:(lia)). pose proof (req_size_pos n2 ltac:(lia)). lia.
Qed.

Lemma dg_blocks_iv : forall ly S (W : world SEGS) mem md b1 b2,
AR SEGS B ly S W mem md -> In b1 (ablocks B ly S) -> In b2 (ablocks B ly S) -> b1 <> b2 ->
iv_apart (fst b1) (snd b1) (fst b2) (snd b2).
Proof.
intros ly S W mem md [p1 n1] [p2 n2] HAR H1 H2 Hne.
pose proof (dg_blocks_apart ly S W mem md _ _ HAR H1 H2 Hne) as Hd. unfold zdisjoint, iv_apart in *. cbn [fst snd] in *.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p1 n1 HAR H1) as (_ & _ & _ & _ & _ & _ & Hn1).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p2 n2 HAR H2) as (_ & _ & _ & _ & _ & _ & Hn2).
pose proof (req_size_pos n1 ltac:(lia)). pose proof (req_size_pos n2 ltac:(lia)). lia.
Qed.

(* the block lists of the post (descriptors_get_c.v:105-116), from the lists the walk meets: L0 at the entry, Lc after
   record() (F freed), L3 after xstrdup's copy (p, kx), Lf after answer (the old answer freed, (p1, n) the recorder's
   copy, (p2, n) the caller's) *)
Lemma dg_post_blocks : forall (L0 Lc L3 Lf F QL OT O O' : list (Z * Z)) (p kx p1 p2 n old : Z),
Permutation L0 (Lc ++ F) -> (forall pn, In pn F -> In pn O) ->
(forall pn, In pn QL -> In pn O) -> (forall pn, In pn QL -> In pn Lc) ->
(forall pn, In pn O -> In pn Lc -> In pn QL) ->
Permutation L3 ((p, kx) :: Lc) -> Forall (fun qk => iv_apart p kx (fst qk) (snd qk)) Lc -> 1 <= kx ->
Permutation OT (QL ++ [(p, kx)]) ->
(old = 0 \/ exists m, In (old, m) QL) ->
(forall b1 b2, In b1 L3 -> In b2 L3 -> fst b1 = fst b2 -> b1 = b2) -> (forall b, In b L3 -> 4096 <= fst b) ->
(forall pn, In pn L3 -> fst pn <> old -> pn <> (p1, n) /\ pn <> (p2, n)) -> p1 <> p2 ->
(forall pn, In pn Lf <-> (In pn L3 /\ fst pn <> old) \/ pn = (p1, n) \/ pn = (p2, n)) ->
(forall pn, In pn O' <-> (In pn OT /\ fst pn <> old) \/ pn = (p1, n)) ->
(forall b1 b2, In b1 Lf -> In b2 Lf -> fst b1 = fst b2 -> b1 = b2) ->
(forall b1 b2, In b1 Lf -> In b2 Lf -> b1 <> b2 -> iv_apart (fst b1) (snd b1) (fst b2) (snd b2)) ->
(forall pn, In pn O' -> In pn O \/ ~ In pn L0) /\
(forall pn, In pn L0 -> ~ In pn O -> pn <> (p2, n)) /\ ~ In p2 (map fst O') /\
(forall pn, In pn L0 -> ~ In pn O -> In pn Lf /\ iv_apart (fst pn) (snd pn) p2 n) /\
(forall pn, In pn Lf -> (In pn L0 /\ ~ In pn O) \/ In pn O' \/ pn = (p2, n)).
Proof.
intros L0 Lc L3 Lf F QL OT O O' p kx p1 p2 n old HP0 HFO HQO HQc HOQ HP3 HFr Hkx HOT Hold Hst3 H4096 HGf H12 HLf HO' Hstf Hapf.
assert (L3c : forall pn, In pn Lc -> In pn L3) by (intros pn H; apply (Permutation_in _ (Permutation_sym HP3)); right; exact H).
assert (L3p : In (p, kx) L3) by (apply (Permutation_in _ (Permutation_sym HP3)); left; reflexivity).
assert (L0s : forall pn, In pn L0 -> In pn Lc \/ In pn F)
  by (intros pn H; apply in_app_iff; exact (Permutation_in _ HP0 H)).
assert (Lc0 : forall pn, In pn Lc -> In pn L0)
  by (intros pn H; apply (Permutation_in _ (Permutation_sym HP0)); apply in_app_iff; left; exact H).
assert (OTs : forall pn, In pn OT -> In pn QL \/ pn = (p, kx)).
{ intros pn H. apply (Permutation_in _ HOT) in H. apply in_app_iff in H as [H | [<- | []]]; [left; exact H | right; reflexivity]. }
assert (OT3 : forall pn, In pn OT -> In pn L3) by (intros pn H; destruct (OTs pn H) as [H' | ->]; [exact (L3c pn (HQc pn H')) | exact L3p]).
(* a start that is old belongs to a block of QL only *)
assert (Hold3 : forall pn, In pn L3 -> fst pn = old -> In pn QL).
{ intros pn H He. destruct Hold as [-> | (m & Hm)]; [pose proof (H4096 pn H); lia|].
  rewrite (Hst3 pn (old, m) H (L3c _ (HQc _ Hm)) He). exact Hm. }
(* the copy (p, kx) is no block of Lc *)
assert (Hpc : ~ In (p, kx) Lc).
{ intros H. rewrite Forall_forall in HFr. specialize (HFr _ H). unfold iv_apart in HFr. cbn [fst snd] in HFr. lia. }
split; [|split; [|split; [|split]]].
- intros pn H. apply HO' in H as [(H & _) | ->].
  + destruct (OTs pn H) as [H' | ->]; [left; exact (HQO _ H')|].
    destruct (in_dec dg_pz_dec (p, kx) L0) as [H0|H0]; [|right; exact H0].
    destruct (L0s _ H0) as [Hc | Hf]; [exfalso; exact (Hpc Hc) | left; exact (HFO _ Hf)].
  + destruct (in_dec dg_pz_dec (p1, n) L0) as [H0|H0]; [|right; exact H0].
    destruct (L0s _ H0) as [Hc | Hf]; [| left; exact (HFO _ Hf)].
    destruct (Z.eq_dec p1 old) as [Ho | Ho]; [left; exact (HQO _ (Hold3 _ (L3c _ Hc) Ho))|].
    exfalso. exact (proj1 (HGf _ (L3c _ Hc) Ho) eq_refl).
- intros pn H0 HnO Ep. subst pn. destruct (L0s _ H0) as [Hc | Hf]; [| exact (HnO (HFO _ Hf))].
  assert (Hne : p2 <> old) by (intros He; exact (HnO (HQO _ (Hold3 _ (L3c _ Hc) He)))).
  exact (proj2 (HGf _ (L3c _ Hc) Hne) eq_refl).
- intros H. apply in_map_iff in H as (pn & Hpn & H).
  assert (Hf2 : In (p2, n) Lf) by (apply HLf; right; right; reflexivity).
  apply HO' in H as [(H & Hne) | ->].
  + assert (Hf : In pn Lf) by (apply HLf; left; split; [exact (OT3 pn H) | exact Hne]).
    pose proof (Hstf pn (p2, n) Hf Hf2 Hpn) as Ep. subst pn. exact (proj2 (HGf _ (OT3 _ H) Hne) eq_refl).
  + cbn [fst] in Hpn. exact (H12 Hpn).
- intros pn H0 HnO. destruct (L0s _ H0) as [Hc | Hf]; [| exfalso; exact (HnO (HFO _ Hf))].
  assert (Hne : fst pn <> old) by (intros He; exact (HnO (HQO _ (Hold3 _ (L3c _ Hc) He)))).
  assert (Hf : In pn Lf) by (apply HLf; left; split; [exact (L3c _ Hc) | exact Hne]).
  split; [exact Hf|].
  apply (Hapf pn (p2, n) Hf ltac:(apply HLf; right; right; reflexivity)).
  intros Ep. subst pn. exact (proj2 (HGf _ (L3c _ Hc) Hne) eq_refl).
- intros pn H. apply HLf in H as [(H & Hne) | [-> | ->]].
  + apply (Permutation_in _ HP3) in H as [<- | Hc].
    * right; left. apply HO'. left. split; [|exact Hne]. apply (Permutation_in _ (Permutation_sym HOT)).
      apply in_app_iff. right. left. reflexivity.
    * destruct (in_dec dg_pz_dec pn O) as [HinO | HnO].
      -- right; left. apply HO'. left. split; [|exact Hne]. apply (Permutation_in _ (Permutation_sym HOT)).
         apply in_app_iff. left. exact (HOQ _ HinO Hc).
      -- left. split; [exact (Lc0 _ Hc) | exact HnO].
  + right; left. apply HO'. right. reflexivity.
  + right; right. reflexivity.
Qed.

(* a string argument survives a change of memory outside the program's statics: its bytes are a live block's or
   read-only image bytes; the rest of astr_argA does not read memory *)
Lemma dg_argA_kept : forall ly S (W : world SEGS) mem md (rd' : reader) O q v,
AR SEGS B ly S W mem md ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O q (Some v) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Exists (in_zr a) recb_PG -> rd' a = rdW W mem a) ->
astr_argA B ly S rd' (in_roP SEGS RLO RHI) O q (Some v).
Proof.
intros ly S W mem md rd' O q v HAR (Hq0 & [Hs Hnz] & Hn & Harm) HK. cbn zeta in *.
assert (Hb : forall i, 0 <= i < Z.of_nat (length v) + 1 -> 0 <= q + i < 2 ^ 64 /\ ~ Exists (in_zr (q + i)) recb_PG).
{ intros i Hi. destruct Harm as [(HB1 & _) | (HR & _)].
  - destruct (dg_blk_off ly S W mem md q _ HAR HB1 (q + i) ltac:(lia)) as (Hr & Hnp & _). split; [lia | exact Hnp].
  - destruct (HR i Hi) as (Hro & _). destruct (cmd_ro_prog_apart _ Hro) as [Himg Hnp].
    pose proof (pa_img_range _ Himg). split; [lia | exact Hnp]. }
split; [exact Hq0|]. split; [|split; [exact Hn | exact Harm]].
split; [|exact Hnz]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
destruct (Hb (Z.of_nat i) ltac:(lia)) as [Hb1 Hb2]. rewrite (HK _ Hb1 Hb2).
exact (Hs i ltac:(rewrite length_app; cbn [length]; lia)).
Qed.

(* a block answer frees: one of the list, at the old answer's start *)
Lemma dg_in_filter : forall (old : Z) (L : list (Z * Z)) pn,
In pn (filter (fun pn : Z * Z => fst pn =? old) L) -> In pn L /\ fst pn = old.
Proof.
intros old L pn. induction L as [|y L IH]; intros H; [cbn in H; contradiction|].
cbn in H. destruct (decide _) as [Hd | Hd] in H.
- destruct H as [<- | H].
  + split; [left; reflexivity|]. apply Z.eqb_eq. destruct (fst y =? old); [reflexivity | first [destruct Hd | discriminate Hd]].
  + destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
- destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
Qed.

Lemma dg_bv5 : forall r (b : bv 5), bv_unsigned b = r -> Z_to_bv 5 r = b.
Proof.
intros r b H. apply bv_eq. rewrite Z_to_bv_unsigned, <- H. unfold bv_wrap.
pose proof (bv_unsigned_in_range 5 b) as Hb. apply Z.mod_small. exact Hb.
Qed.

Lemma dg_walkJ : dg_walkJ_stmt.
Proof.
unfold dg_walkJ_stmt.
intros ly S W regs mem md ch pu uri R O lyc Sc Wc regs1 memc mdc k c HPRE HFRM HROD0 Hpu HO Hfr8 HEV HLV HMOK
  HJ Hk HMLE HRG HFR Hc HSJ HMD.
destruct HSJ as (x & -> & XB & XS & XL).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (HTS : DESCRIPTORS_GET_STK = 16592) by (vm_compute; reflexivity).
pose proof HJ as (HAR & HLY & _ & _ & _ & Hfrs & Hnev & Hk0 & _ & _ & _ & _ & _ & Hpres & _ & _ & HQTc).
pose proof HRG as (R2 & R3 & R4 & R8 & R9 & R19 & Rhi).
destruct (dg_slot_bounds c Hc) as [Hcb Hc8].
destruct HMD as (F & blb & rdb & Rb & Qb & HA0 & HRR & HCS & HNC & HKG & HKB & HQO & HPF & HFO & HOQ & HF16).
destruct (dg_blk_off lyc Sc Wc memc mdc pu _ HAR XB pu ltac:(lia)) as (Hpu4 & _ & _).
(* the reply text, and the budgets the callees ask for *)
set (tA := snd (rec_answer (rec_record R REC_DESCRIPTORS_GET [x]) (REC_DESCRIPTORS_GET, [x]) (shape_of dg_verb) false)).
assert (HEV' : st_nev S + (rec_spill_frees R + EV_XSTRDUP + EV_ANSWER) <= EV_MAX) by exact HEV.
assert (HLV' : blocks_bytes S + (LIVE_XSTRDUP x + LIVE_ANSWER tA) <= LIVE_MAX) by exact HLV.
assert (HMOK' : mo_ok MT S (rec_spill_frees R * mo_free MT + XM_XSTRDUP MT x + XM_ANSWER MT tA)) by exact HMOK.
assert (HBB : blocks_bytes Sc <= blocks_bytes S) by exact (dg_bytes_le ly S W mem md lyc Sc F HAR0 HPF).
assert (BEVx : st_nev Sc + EV_XSTRDUP <= EV_MAX) by (unfold EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in *; lia).
assert (BLVx : blocks_bytes Sc + LIVE_XSTRDUP x <= LIVE_MAX).
{ unfold LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XSTRDUP in *. pose proof (Nat2Z.is_nonneg (length tA)). lia. }
assert (XMA : 0 <= XM_ANSWER MT tA).
{ unfold XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length tA) + 1) ltac:(lia)). lia. }
assert (XMX : 0 <= XM_XSTRDUP MT x) by (unfold XM_XSTRDUP; apply (mo_malloc_nonneg MT MTL); lia).
assert (BMx : mo_ok MT Sc (XM_XSTRDUP MT x))
  by (apply (mok_station MT S Sc _ (rec_spill_frees R * mo_free MT) _ MTL HMOK' HMLE XMX); lia).
(* the symbolic state at the join *)
destruct (dg_seedJ B HB cmd_prog_writable lyc Sc Wc memc mdc regs regs1 (spZ regs) c pu true HAR
  ltac:(rewrite HTS in Hslo; lia) Hal16 ltac:(intros a Ha; apply Hpres; rewrite HTS; lia) R2 R8 R9 R19 Hc
  ltac:(cbn; lia) Hpu HFR) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 (dg_extra regs)))) by apply Eimg_env.
assert (EL : forall n, (n < A_TEXT)%nat -> ew (Eimg (Ereg regs1 (dg_extra regs))) n = ew (Ereg regs1 (dg_extra regs)) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
remember (Eimg (Ereg regs1 (dg_extra regs))) as E eqn:HE.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 6)%nat -> ew E (32 + j) = nth j (dg_extra regs) (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 48)
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; rewrite HTS in Hslo; lia).
assert (U8 : bv_unsigned (ew E 8) = c)
  by (rewrite (EE 8%nat 8%bv eq_refl), R8; apply unsigned_lit_small; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
(* 0x8d014 .. 0x8d054: checks 1 and 2, c->fn := 23, c->nargs := 0, and the call of xstrdup *)
paj_run_tok RUN HS HJ SHOK dg_Bspan;
  [ lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ =>
      let rs' := eval vm_compute in rs in change rs with rs' end;
    apply awr_ok_cons_ro; [cbn; lia|];
    apply (dg_awr_slot _ _ _ _ _ _ _ _ _ _ c); [exact U8 | exact Hc | apply awr_ok_nil] |].
match goal with |- context [with_vm_backing ?a ?b ?c] => set (md1 := with_vm_backing a b c) in *; clearbody md1 end.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
assert (Q10' : getr (ms_regs ms) 10 = w64 pu) by (rewrite Q10, (EE 9%nat 9%bv eq_refl), R9; reflexivity).
pose proof HJ as (HAR1 & _).
assert (FW1 : forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 16) -> rdW Wc (ms_mem ms) a = rdW Wc memc a)
  by (intros a Ha Hn; apply (dg_run_keeps_out E _ (w_H Wc) memc (ms_mem ms) c HFr U8); [dg_wr_tac | exact Ha | exact Hn]).
assert (NSb : forall a, pu <= a < pu + (Z.of_nat (length x) + 1) -> 0 <= a < 2 ^ 64 /\ ~ (c <= a < c + 16)).
{ intros a Ha. destruct (dg_blk_off lyc Sc Wc memc mdc _ _ HAR XB a Ha) as (Hb & Hnp & _).
  split; [lia|]. intros Hs. exact (Hnp (dg_in_PG c a Hc ltac:(unfold CALL_SIZE; lia))). }
assert (XS1 : astr_atR (rdW Wc (ms_mem ms)) pu x).
{ apply (rastr_kept (rdW Wc memc) _ pu x XS). intros i Hi. destruct (NSb (pu + i) ltac:(lia)) as [Hb Hn].
  exact (FW1 _ Hb Hn). }
destruct XB as (qb & kb & Hqb & Hqb1 & Hqb2).
assert (XT1 : atail_vis SEGS Wc (ms_mem ms) (pu + Z.of_nat (length x)))
  by exact (cmd_heap_tail_vis lyc Sc Wc (ms_mem ms) md1 qb kb (pu + Z.of_nat (length x)) HAR1 Hqb ltac:(lia)).
assert (XA1 : astr_argA B lyc Sc (rdW Wc (ms_mem ms)) (in_roP SEGS RLO RHI) [] pu (Some x)).
{ unfold astr_argA. split; [lia|]. split; [exact XS1|]. split; [exact XL|].
  left. split; [exists qb, kb; split; [exact Hqb | lia] | constructor]. }
(* 0x8d054: the call of xstrdup on the string *)
lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rg _ ?mm _; cfg_model := ?mdq |} _ =>
  assert (Qsp : spZ rg = spZ regs + -48) by (unfold spZ at 1; rewrite Q2, Usp; lia);
  assert (Q3' : getr rg 3 = w64 (as_gp B)) by (rewrite Q3, (EE 3%nat 3%bv eq_refl), R3; exact Hgp);
  assert (Q4' : getr rg 4 = w64 (as_tp B)) by (rewrite Q4, (EE 4%nat 4%bv eq_refl), R4; exact Htp);
  assert (Qs0 : achain lyc (aview SEGS (w_H Wc) mm) (spZ regs + -48) (s0Z rg) [])
    by (apply achain_low; unfold s0Z; rewrite Q8, U8; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia);
  eapply SRr_bind;
  [ eapply (cl_callS B LAWS Wc rg mm _ DESCRIPTORS_GET_STK (spZ regs) (dg_FP O) ly S W mem md [] lyc Sc mdq k
      XSTRDUP_STK [] EV_XSTRDUP (-48) (getr rg 1) []
      (fun ly3 S3 W3 regs3 mem3 md3 => exists p : Z,
        getr regs3 10 = w64 p /\ 4096 <= p < 2 ^ 64 /\
        Permutation (ablocks B ly3 S3) ((p, LIVE_XSTRDUP x) :: ablocks B lyc Sc) /\
        Forall (fun qk => iv_apart p (LIVE_XSTRDUP x) (fst qk) (snd qk)) (ablocks B lyc Sc) /\
        in_blockA (ablocks B ly3 S3) p (LIVE_XSTRDUP x) /\
        astr_atR (rdW W3 mem3) p x /\ astr_atR (rdW W3 mem3) pu x /\
        blocks_bytes S3 <= blocks_bytes Sc + LIVE_XSTRDUP x /\
        mo_le MT Sc S3 (XM_XSTRDUP MT x)) HJ Qsp);
    [ reflexivity | lia | unfold XSTRDUP_STK, ASTACK; lia | rewrite HTS; unfold XSTRDUP_STK, ASTACK; lia
    | exact Q3' | exact Q4' | reflexivity
    | rewrite Q1; apply ret_ok_codeptr_v; [cbv; split; [congruence | reflexivity] | reflexivity]
    | rewrite Q1, unsigned_lit_small by lia; lia
    | exact Qs0
    | intros HPRE1; rewrite dg_sig_xstrdup; eapply SRr_mono;
      [ exact (TXSTRDUP fx lyc Sc Wc rg mm mdq [] pu x HPRE1
          (dg_aro_at ly S W mem md lyc Sc Wc mm mdq O k _ HJ HAR0 HO HROD0) Q10' (or_introl XA1) XT1 BEVx BLVx BMx)
      | cbv beta; unfold apost_base; intros Wx cx _ (lyx & Sx & regsx & memx & mdx & -> & HJ1 & HP & HK3);
        exists lyx, Sx, regsx, memx, mdx; split; [reflexivity | split; [exact HJ1 | split; [exact HP | exact HK3]]] ]
    | intros a (r & Hr & _); destruct Hr ]
  | ] end.
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & p & Ha02 & Hp4096 & HPerm2 &
  HFresh2 & Hpin2b & Hpx2 & Hsx2 & HBB2 & MLE2).
pose proof (proj1 HJ2) as HAR2.
(* back at 0x8d058: the frame and the slot are kept by xstrdup (its footprint is empty) *)
jafter_call_keep_pi HS 38%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha.
    + rewrite Usp in Ha. apply (mbyte_of_aview SEGS). apply (dg_call_kept _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc2).
      left. split; [lia|]. rewrite HTS in Hslo. lia.
    + lia.
  - apply (dg_region_kept_slot _ _ _ _ _ _ _ _ _ _ _ _ _ _ c _ HJc2 U8 Hc). }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS. rewrite Q1.
remember (havoc E 38 (map (getr regs2) CLOB)) as E2 eqn:HE2.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [assumption | cbv; lia]).
assert (OLD2 : forall n, (n < 38)%nat -> ew E2 n = ew E n) by (intros n Hn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hn).
assert (A42 : ew E2 42 = getr regs2 10) by (rewrite HE2; reflexivity).
assert (U8b : bv_unsigned (ew E2 8) = c) by (rewrite OLD2 by lia; exact U8).
assert (SHOK2 : sh_ok SEGS dg_Bx dg_SH E2 (mrestrict (w_H W2) mem2))
  by (apply (dg_shok E2 ly2 S2 W2 mem2 md2 c HAR2 Hc);
      [rewrite OLD2 by lia; rewrite (EE 19%nat 19%bv eq_refl); exact R19
      | rewrite OLD2 by lia; rewrite (EE 8%nat 8%bv eq_refl); exact R8]).
(* 0x8d058 .. 0x8d098: check 3, c->nargs := 1, check 4, c->args[0] := the copy, and the call of rec_shape_of *)
paj_run_tok RUN HS HJ2 SHOK2 dg_Bspan;
  [ lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ =>
      let rs' := eval vm_compute in rs in change rs with rs' end;
    apply awr_ok_cons_ro; [cbn; lia|];
    apply (dg_awr_slot _ _ _ _ _ _ _ _ _ _ c); [exact U8b | exact Hc | apply awr_ok_nil] |].
match goal with |- context [with_vm_backing ?a ?b ?c] => set (md3 := with_vm_backing a b c) in *; clearbody md3 end.
pmkst HS.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11.
assert (T10' : getr (ms_regs ms0) 10 = w64 0x21f60)
  by (rewrite T10, <- (Z_to_bv_bv_unsigned 64 (ew E2 317)), (HEI2 317%nat ltac:(cbv; lia)), <- dg_verb_atom, dg_verb_val;
      reflexivity).
assert (T11' : getr (ms_regs ms0) 11 = w64 (Z.of_nat (length dg_verb))) by (rewrite T11; reflexivity).
pose proof HJ2 as (HAR2' & _ & _ & _ & _ & _ & Hnev2 & _).
assert (BEVr : st_nev S2 + EV_REC_SHAPE_OF <= EV_MAX)
  by (unfold EV_REC_SHAPE_OF, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in *; lia).
(* 0x8d098: the call of rec_shape_of on the verb "descriptor_get" *)
lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rg _ ?mm _; cfg_model := ?mdq |} _ =>
  assert (Tsp : spZ rg = spZ regs + -48) by (unfold spZ at 1; rewrite T2, OLD2, Usp by lia; lia);
  assert (T3' : getr rg 3 = w64 (as_gp B)) by (rewrite T3, OLD2, (EE 3%nat 3%bv eq_refl), R3 by lia; exact Hgp);
  assert (T4' : getr rg 4 = w64 (as_tp B)) by (rewrite T4, OLD2, (EE 4%nat 4%bv eq_refl), R4 by lia; exact Htp);
  assert (HROD2 : arodata_okP SEGS RLO RHI B (rdW W2 mm))
    by exact (dg_aro_at ly S W mem md ly2 S2 W2 mm mdq O _ _ HJ2 HAR0 HO HROD0);
  assert (HRO2 : cmd_ro_ok (rdW W2 mm)) by exact (cmd_ro_ok_of_aro ly2 S2 W2 mm mdq HAR2' HROD2);
  destruct (dg_verb_arg ly2 S2 W2 mm HRO2) as (VB & VA);
  eapply SRr_bind;
  [ eapply (cl_callS_na B LAWS W2 rg mm _ DESCRIPTORS_GET_STK (spZ regs) (dg_FP O) ly S W mem md [] ly2 S2 mdq _
      REC_SHAPE_OF_STK [] EV_REC_SHAPE_OF (-48) (getr rg 1)
      (fun ly3 S3 W3 regs3 mem3 md3 =>
        (exists q, getr regs3 10 = w64 q /\ 0 <= q < 2 ^ 64 /\
          forall O0, astr_argA B ly3 S3 (rdW W3 mem3) (in_roP SEGS RLO RHI) O0 q (Some (shape_of dg_verb))) /\
        Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) /\ ly3 = ly2 /\ S3 = S2) HJ2 Tsp);
    [ reflexivity | lia | vm_compute; congruence | rewrite HTS; vm_compute; congruence
    | exact T3' | exact T4' | reflexivity
    | rewrite T1; apply ret_ok_codeptr_v; [cbv; split; [congruence | reflexivity] | reflexivity]
    | rewrite T1, unsigned_lit_small by lia; lia
    | intros HPRE1; rewrite dg_sig_rec_shape_of; eapply SRr_mono;
      [ exact (TREC_SHAPE_OF fx ly2 S2 W2 rg mm mdq 0x21f60 dg_verb HPRE1 HROD2 T10' ltac:(lia) T11'
          ltac:(vm_compute; reflexivity) HRO2 VOBJS (fun _ => conj VB (or_intror VA)) BEVr)
      | cbv beta; unfold apost_base; intros Wx cx _ (lyx & Sx & regsx & memx & mdx & -> & HJ1 & HP & HK3);
        exists lyx, Sx, regsx, memx, mdx; split; [reflexivity | split; [exact HJ1 | split; [exact HP | exact HK3]]] ]
    | intros a (r & Hr & _); destruct Hr ]
  | ] end.
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md4 & -> & HJ3 & HJc3 & HP3 &
  (q & Hq10 & Hq64 & HqA) & HPerm3 & -> & ->).
pose proof (proj1 HJ3) as HAR3.
(* back at 0x8d09c: the frame and the slot are kept by rec_shape_of (its footprint is empty) *)
jafter_call_keep_pi HS 60%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0; 1]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha.
    + rewrite OLD2, Usp in Ha by lia. apply (mbyte_of_aview SEGS).
      apply (dg_call_kept _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc3). left. split; [lia|]. rewrite HTS in Hslo. lia.
    + lia.
  - apply (dg_region_kept_slot _ _ _ _ _ _ _ _ _ _ _ _ _ _ c _ HJc3 U8b Hc). }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS. rewrite T1.
remember (havoc E2 60 (map (getr regs3) CLOB)) as E3 eqn:HE3.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [assumption | cbv; lia]).
assert (OLD3' : forall n, (n < 60)%nat -> ew E3 n = ew E2 n) by (intros n Hn; rewrite HE3; apply YN3v.ew_havoc_old; exact Hn).
assert (OLD3 : forall n, (n < 38)%nat -> ew E3 n = ew E n) by (intros n Hn; rewrite OLD3' by lia; exact (OLD2 n Hn)).
assert (A64 : ew E3 64 = getr regs3 10) by (rewrite HE3; reflexivity).
assert (U8c : bv_unsigned (ew E3 8) = c) by (rewrite OLD3 by lia; exact U8).
assert (SHOK3 : sh_ok SEGS dg_Bx dg_SH E3 (mrestrict (w_H W3) mem3))
  by (apply (dg_shok E3 ly2 S2 W3 mem3 md4 c HAR3 Hc);
      [rewrite OLD3 by lia; rewrite (EE 19%nat 19%bv eq_refl); exact R19
      | rewrite OLD3 by lia; rewrite (EE 8%nat 8%bv eq_refl); exact R8]).
(* 0x8d09c .. 0x8d0c4: a1 := the shape, a0 := c, a2 := 0, the frame restored, and the tail jump into answer *)
paj_run_tok RUN HS HJ3 SHOK3 dg_Bspan;
  [ lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ =>
      let rs' := eval vm_compute in rs in change rs with rs' end;
    apply awr_ok_cons_ro; [cbn; lia|];
    apply (dg_awr_slot _ _ _ _ _ _ _ _ _ _ c); [exact U8c | exact Hc | apply awr_ok_nil] |].
match goal with |- context [with_vm_backing ?a ?b ?c] => set (md5 := with_vm_backing a b c) in *; clearbody md5 end.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (12%bv : bv 5) P12. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24.
prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
(* the callee-saved registers at the tail jump are the caller's: sp back at the entry's, gp tp and s5 .. s11 kept
   since the join, ra and s0 .. s4 reloaded from the frame *)
assert (HPRT : aregs_preserved regs (ms_regs ms1)).
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hcs : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  clear Hr.
  destruct Hcs as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
  - rewrite (dg_bv5 2 2%bv eq_refl). rewrite P2, OLD3, Usp by lia.
    replace (spZ regs - 48 + 48) with (spZ regs) by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
  - rewrite (dg_bv5 3 3%bv eq_refl). rewrite P3, OLD3, (EE 3%nat 3%bv eq_refl), R3 by lia. reflexivity.
  - rewrite (dg_bv5 4 4%bv eq_refl). rewrite P4, OLD3, (EE 4%nat 4%bv eq_refl), R4 by lia. reflexivity.
  - rewrite (dg_bv5 8 8%bv eq_refl). rewrite P8, OLD3 by lia. change 33%nat with (32 + 1)%nat.
    rewrite EX by lia. cbn [dg_extra dg_saved map nth]. rewrite (dg_bv5 8 8%bv eq_refl). reflexivity.
  - rewrite (dg_bv5 9 9%bv eq_refl). rewrite P9, OLD3 by lia. change 34%nat with (32 + 2)%nat.
    rewrite EX by lia. cbn [dg_extra dg_saved map nth]. rewrite (dg_bv5 9 9%bv eq_refl). reflexivity.
  - rewrite (dg_bv5 18 18%bv eq_refl). rewrite P18, OLD3 by lia. change 35%nat with (32 + 3)%nat.
    rewrite EX by lia. cbn [dg_extra dg_saved map nth]. rewrite (dg_bv5 18 18%bv eq_refl). reflexivity.
  - rewrite (dg_bv5 19 19%bv eq_refl). rewrite P19, OLD3 by lia. change 36%nat with (32 + 4)%nat.
    rewrite EX by lia. cbn [dg_extra dg_saved map nth]. rewrite (dg_bv5 19 19%bv eq_refl). reflexivity.
  - rewrite (dg_bv5 20 20%bv eq_refl). rewrite P20, OLD3 by lia. change 37%nat with (32 + 5)%nat.
    rewrite EX by lia. cbn [dg_extra dg_saved map nth]. rewrite (dg_bv5 20 20%bv eq_refl). reflexivity.
  - rewrite (dg_bv5 21 21%bv eq_refl). rewrite P21, OLD3, (EE 21%nat 21%bv eq_refl) by lia.
    rewrite <- (dg_bv5 21 21%bv eq_refl). exact (Rhi 21 ltac:(lia)).
  - rewrite (dg_bv5 22 22%bv eq_refl). rewrite P22, OLD3, (EE 22%nat 22%bv eq_refl) by lia.
    rewrite <- (dg_bv5 22 22%bv eq_refl). exact (Rhi 22 ltac:(lia)).
  - rewrite (dg_bv5 23 23%bv eq_refl). rewrite P23, OLD3, (EE 23%nat 23%bv eq_refl) by lia.
    rewrite <- (dg_bv5 23 23%bv eq_refl). exact (Rhi 23 ltac:(lia)).
  - rewrite (dg_bv5 24 24%bv eq_refl). rewrite P24, OLD3, (EE 24%nat 24%bv eq_refl) by lia.
    rewrite <- (dg_bv5 24 24%bv eq_refl). exact (Rhi 24 ltac:(lia)).
  - rewrite (dg_bv5 25 25%bv eq_refl). rewrite P25, OLD3, (EE 25%nat 25%bv eq_refl) by lia.
    rewrite <- (dg_bv5 25 25%bv eq_refl). exact (Rhi 25 ltac:(lia)).
  - rewrite (dg_bv5 26 26%bv eq_refl). rewrite P26, OLD3, (EE 26%nat 26%bv eq_refl) by lia.
    rewrite <- (dg_bv5 26 26%bv eq_refl). exact (Rhi 26 ltac:(lia)).
  - rewrite (dg_bv5 27 27%bv eq_refl). rewrite P27, OLD3, (EE 27%nat 27%bv eq_refl) by lia.
    rewrite <- (dg_bv5 27 27%bv eq_refl). exact (Rhi 27 ltac:(lia)). }
assert (Hraw : getr (ms_regs ms1) 1 = getr regs 1).
{ rewrite P1, OLD3 by lia. change 32%nat with (32 + 0)%nat. rewrite EX by lia.
  cbn [dg_extra dg_saved map nth]. rewrite (dg_bv5 1 1%bv eq_refl). reflexivity. }
(* the slot's three fields at the tail jump *)
pose proof (st_ok_region_nth E3 _ _ 1 _ HS eq_refl) as HRf. cbn [ms_mem restrict] in HRf.
match type of HRf with region_ok _ _ _ ?r => let r' := eval vm_compute in r in change r with r' in HRf end.
pose proof (field_of_region_any E3 _ 8%nat c _ _ _ _ _ 0 4 (SLit 23) HRf U8c ltac:(cbn; tauto) ltac:(cbn; lia)) as G0.
pose proof (field_of_region_any E3 _ 8%nat c _ _ _ _ _ 4 4 (SLit 1) HRf U8c ltac:(cbn; tauto) ltac:(cbn; lia)) as G4.
pose proof (field_of_region_any E3 _ 8%nat c _ _ _ _ _ 8 8 (SOff 42 0) HRf U8c ltac:(cbn; tauto) ltac:(cbn; lia)) as G8.
clear HRf.
pose proof HJ3 as (HART & HLYT & _ & _ & _ & HfrT & HnevT & _).
assert (Hpin2 : In (p, LIVE_XSTRDUP x) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym HPerm2)); left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hpin2) as (_ & Hp4k & Hpceil & _ & _ & _ & Hkx).
pose proof (req_size_pos (LIVE_XSTRDUP x) ltac:(lia)) as Hreqx.
assert (D0 : bv_unsigned (sv_denot E3 (SLit 23)) mod 2 ^ (8 * Z.of_N 4) = 23)
  by (change (sv_denot E3 (SLit 23)) with (Z_to_bv 64 23); rewrite unsigned_lit_small by lia; reflexivity).
assert (D4 : bv_unsigned (sv_denot E3 (SLit 1)) mod 2 ^ (8 * Z.of_N 4) = 1)
  by (change (sv_denot E3 (SLit 1)) with (Z_to_bv 64 1); rewrite unsigned_lit_small by lia; reflexivity).
assert (E42 : ew E3 42 = Z_to_bv 64 p) by (rewrite OLD3', A42, Ha02 by lia; reflexivity).
assert (D8 : bv_unsigned (sv_denot E3 (SOff 42 0)) mod 2 ^ (8 * Z.of_N 8) = p)
  by (cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia; apply Z.mod_small; cbn; lia).
rewrite D0 in G0. rewrite D4 in G4. rewrite D8 in G8.
apply (aval_mem_view SEGS) in G0, G4, G8.
(* what the runs and the two calls since the join kept *)
assert (FW2 : forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 16) -> rdW W2 (ms_mem ms0) a = rdW W2 mem2 a)
  by (intros a Ha Hn; apply (dg_run_keeps_out E2 _ (w_H W2) mem2 (ms_mem ms0) c HFr0 U8b); [dg_wr_tac | exact Ha | exact Hn]).
assert (FW3 : forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 16) -> rdW W3 (ms_mem ms1) a = rdW W3 mem3 a)
  by (intros a Ha Hn; apply (dg_run_keeps_out E3 _ (w_H W3) mem3 (ms_mem ms1) c HFr1 U8c); [dg_wr_tac | exact Ha | exact Hn]).
assert (CK1 : forall a, Exists (in_zr a) recb_PG -> rdW W2 mem2 a = rdW Wc (ms_mem ms) a)
  by (intros a HP; exact (dg_call_kept _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc2 (or_intror HP))).
assert (CK2 : forall a, Exists (in_zr a) recb_PG -> rdW W3 mem3 a = rdW W2 (ms_mem ms0) a)
  by (intros a HP; exact (dg_call_kept _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc3 (or_intror HP))).
assert (KPG : forall a, Exists (in_zr a) recb_PG -> ~ (c <= a < c + 16) -> rdW W3 (ms_mem ms1) a = rdW Wc memc a).
{ intros a HP Hn. pose proof (dg_PG_range a HP) as Ha. unfold A_G_REC, A_G_QUITTING in Ha.
  rewrite (FW3 a ltac:(lia) Hn), (CK2 a HP), (FW2 a ltac:(lia) Hn), (CK1 a HP), (FW1 a ltac:(lia) Hn). reflexivity. }
assert (NS : forall a, ~ Exists (in_zr a) recb_PG -> ~ (c <= a < c + 16))
  by (intros a Hn Hs; exact (Hn (dg_in_PG c a Hc ltac:(unfold CALL_SIZE; lia)))).
assert (KBL : forall pb nb i, In (pb, nb) (ablocks B lyc Sc) -> 0 <= i < req_size nb ->
  rdW W3 (ms_mem ms1) (pb + i) = rdW Wc memc (pb + i)).
{ intros pb nb i Hin Hi.
  assert (Hin2 : In (pb, nb) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym HPerm2)); right; exact Hin).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hb4k & Hbceil & _).
  assert (Hnp : ~ Exists (in_zr (pb + i)) recb_PG)
    by (intros HP; exact (recb_heap_noimg_m B lyc Sc Wc memc mdc pb nb (pb + i) HAR Hin ltac:(lia) (cmd_prog_img _ HP))).
  pose proof (NS _ Hnp) as Hns.
  rewrite (FW3 (pb + i) ltac:(lia) Hns), (dg_call_kept_blk _ _ _ _ _ _ _ _ _ _ _ _ _ pb nb i HJc3 Hin2 Hin2 Hi),
    (FW2 (pb + i) ltac:(lia) Hns), (dg_call_kept_blk _ _ _ _ _ _ _ _ _ _ _ _ _ pb nb i HJc2 Hin Hin2 Hi),
    (FW1 (pb + i) ltac:(lia) Hns).
  reflexivity. }
assert (KPX : forall i, 0 <= i < req_size (LIVE_XSTRDUP x) -> rdW W3 (ms_mem ms1) (p + i) = rdW W2 mem2 (p + i)).
{ intros i Hi.
  assert (Hnp : ~ Exists (in_zr (p + i)) recb_PG)
    by (intros HP; exact (recb_heap_noimg_m B ly2 S2 W2 mem2 md2 p _ (p + i) HAR2 Hpin2 ltac:(lia) (cmd_prog_img _ HP))).
  pose proof (NS _ Hnp) as Hns.
  rewrite (FW3 (p + i) ltac:(lia) Hns), (dg_call_kept_blk _ _ _ _ _ _ _ _ _ _ _ _ _ p _ i HJc3 Hpin2 Hpin2 Hi),
    (FW2 (p + i) ltac:(lia) Hns). reflexivity. }
(* the recorder at the tail jump: record(FN) and arg_s(c, x) done, rec_record R FN [x] *)
assert (HNT : aval_mem (rdW W3 (ms_mem ms1)) (A_G_REC + OFF_NCALLS) 4
  (Z.of_nat (length (r_calls (rec_record Rb REC_DESCRIPTORS_GET [x]))))).
{ rewrite (dg_rec_record_len Rb REC_DESCRIPTORS_GET [x] []).
  apply (aval_mem_kept (rdW Wc memc)); [exact HNC|].
  intros j Hj. apply KPG.
  - apply recb_grec_in. unfold A_G_REC, OFF_NCALLS, REC_SIZE. lia.
  - unfold A_G_REC, OFF_NCALLS, OFF_CALLS in *. lia. }
assert (HKT : forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
  ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> ~ (c <= a < c + 16) -> rdW W3 (ms_mem ms1) a = rdb a)
  by (intros a Ha Hn1 Hn2; rewrite (KPG a ltac:(destruct Ha; [apply recb_grec_in | apply recb_spill_in]; lia) Hn2);
      exact (HKG a Ha Hn1)).
assert (HBLT : forall pn, In pn (lay_blocks Qb) -> In pn (ablocks B ly2 S2))
  by (intros pn H; destruct (HKB pn H) as [Hin _]; apply (Permutation_in _ (Permutation_sym HPerm2)); right; exact Hin).
assert (HBBT : forall pn i, In pn (lay_blocks Qb) -> 0 <= i < snd pn -> rdW W3 (ms_mem ms1) (fst pn + i) = rdb (fst pn + i)).
{ intros [pb nb] i H Hi. destruct (HKB _ H) as [Hin Hb]. cbn [fst snd] in *.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & _ & _ & _ & _ & _ & Hnb).
  pose proof (req_size_pos nb ltac:(lia)) as [_ Hrq].
  rewrite (KBL pb nb i Hin ltac:(lia)). exact (Hb i Hi). }
assert (HsT : astr_atR (rdW W3 (ms_mem ms1)) p x)
  by (apply (rastr_kept (rdW W2 mem2) _ p x Hpx2); intros i Hi; apply KPX; unfold LIVE_XSTRDUP in *; lia).
assert (Hpn : ~ In p (map fst (lay_blocks Qb))).
{ intros H. apply in_map_iff in H as ([pb nb] & Hpb & H). cbn [fst] in Hpb. subst pb.
  destruct (HKB _ H) as [Hin _].
  assert (Hin2' : In (p, nb) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym HPerm2)); right; exact Hin).
  pose proof (dg_blocks_start ly2 S2 W2 mem2 md2 _ _ HAR2 Hin2' Hpin2 eq_refl) as Heq. injection Heq as Heq.
  rewrite Forall_forall in HFresh2. specialize (HFresh2 _ Hin). unfold iv_apart in HFresh2.
  cbn [fst snd] in HFresh2. subst nb. unfold LIVE_XSTRDUP in *. lia. }
assert (Hag : iv_apart p (LIVE_XSTRDUP x) A_G_REC REC_SIZE)
  by exact (dg_heap_iv ly2 S2 W3 (ms_mem ms1) md5 p (LIVE_XSTRDUP x) A_G_REC REC_SIZE HART Hpin2 ltac:(unfold REC_SIZE; lia)
    (fun a Ha => cmd_prog_img a (recb_grec_in a Ha))).
assert (Has : iv_apart p (LIVE_XSTRDUP x) A_REC_SPILL SC_SIZE)
  by exact (dg_heap_iv ly2 S2 W3 (ms_mem ms1) md5 p (LIVE_XSTRDUP x) A_REC_SPILL SC_SIZE HART Hpin2 ltac:(unfold SC_SIZE; lia)
    (fun a Ha => cmd_prog_img a (recb_spill_in a Ha))).
destruct (arep_record_arg blb (ablocks B ly2 S2) rdb (rdW W3 (ms_mem ms1)) Rb Qb REC_DESCRIPTORS_GET x p
  (LIVE_XSTRDUP x) c HA0 ltac:(unfold REC_DESCRIPTORS_GET, REC_FN_COUNT; lia) HCS HNT G0 G4 G8 HKT HBLT HBBT
  ltac:(lia) Hpin2 ltac:(unfold LIVE_XSTRDUP; lia) HsT ltac:(lia) Hpn Hag Has) as (QT & HAT & HPQ).
rewrite HRR in HAT.
set (RT := rec_record R REC_DESCRIPTORS_GET [x]) in HAT.
assert (HREPT : rec_repA B ly2 S2 (rdW W3 (ms_mem ms1)) RT (lay_blocks QT)) by (exists QT; split; [exact HAT | tauto]).
(* the answer the recorder holds, unchanged since the entry of record() *)
destruct (dg_old _ _ _ _ _ _ HA0) as (old & Hold0 & Hold').
assert (Hold : aval_mem (rdW W3 (ms_mem ms1)) (A_G_REC + OFF_ANSWER) 8 old).
{ apply (aval_mem_kept rdb); [exact Hold0|]. intros j Hj. apply HKT.
  - left. unfold A_G_REC, OFF_ANSWER, REC_SIZE. lia.
  - unfold A_G_REC, OFF_ANSWER, OFF_NCALLS. lia.
  - destruct Hc as [(Hc1 & Hc2 & _) | ->]; unfold A_G_REC, OFF_ANSWER, A_REC_SPILL, CALL_SIZE in *; lia. }
assert (Hold64 : 0 <= old < 2 ^ 64).
{ destruct Hold' as [-> | (m & Hm)]; [lia|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ old m HAR0 (HO _ (HQO _ Hm))) as (_ & H4 & Hce & _ & _ & _ & Hm0).
  pose proof (req_size_pos m ltac:(lia)). lia. }
(* the shape rec_shape_of returned, kept by the last run *)
assert (HshT : astr_argA B ly2 S2 (rdW W3 (ms_mem ms1)) (in_roP SEGS RLO RHI) (lay_blocks QT) q (Some (shape_of dg_verb))).
{ apply (dg_argA_kept ly2 S2 W3 mem3 md4 _ _ _ _ HAR3 (HqA (lay_blocks QT))).
  intros a Ha Hn. exact (FW3 a Ha (NS a Hn)). }
(* the frame chain at the tail jump is the entry's: s0 is the caller's again, and the words at and above the entry's
   sp are kept *)
pose proof HLYT as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & K1T & _).
pose proof Hslo as Hslo'. rewrite HTS in Hslo'.
assert (HchT : achain ly2 (rdW W3 (ms_mem ms1)) (spZ regs + 0) (s0Z (ms_regs ms1)) ch).
{ assert (Es0 : s0Z (ms_regs ms1) = s0Z regs).
  { unfold s0Z. apply (f_equal bv_unsigned). rewrite <- (dg_bv5 8 8%bv eq_refl).
    exact (HPRT 8 ltac:(unfold acallee_saved; lia)). }
  rewrite Es0, Z.add_0_r. apply (achain_ly_top ly ly2 _ _ _ _ Etop).
  apply (achain_kept ly (rdW W mem) _ (spZ regs) (s0Z regs) ch (spZ regs) Hch ltac:(lia) ltac:(lia)).
  intros a Ha. apply K1T; [lia | lia |]. apply (dg_notFP_high ly S W mem md O a HAR0 HO). lia. }
(* the premises of answer's contract at the tail jump *)
assert (HRODT : arodata_okP SEGS RLO RHI B (rdW W3 (ms_mem ms1)))
  by exact (dg_aro_at ly S W mem md ly2 S2 W3 (ms_mem ms1) md5 O _ _ HJ3 HAR0 HO HROD0).
assert (HROT : cmd_ro_ok (rdW W3 (ms_mem ms1))) by exact (cmd_ro_ok_of_aro ly2 S2 W3 (ms_mem ms1) md5 HART HRODT).
assert (P10' : getr (ms_regs ms1) 10 = w64 c) by (rewrite P10, OLD3, (EE 8%nat 8%bv eq_refl), R8 by lia; reflexivity).
assert (P11' : getr (ms_regs ms1) 11 = w64 q) by (rewrite P11, A64, Hq10; reflexivity).
assert (P12' : false = negb (bv_unsigned (getr (ms_regs ms1) 12) =? 0))
  by (rewrite P12, unsigned_lit_small by lia; reflexivity).
assert (P3' : getr (ms_regs ms1) 3 = w64 (as_gp B)) by (rewrite P3, OLD3, (EE 3%nat 3%bv eq_refl), R3 by lia; exact Hgp).
assert (P4' : getr (ms_regs ms1) 4 = w64 (as_tp B)) by (rewrite P4, OLD3, (EE 4%nat 4%bv eq_refl), R4 by lia; exact Htp).
assert (Psp : spZ (ms_regs ms1) = spZ regs + 0).
{ unfold spZ at 1. rewrite P2, OLD3, Usp by lia. rewrite unsigned_lit_small by lia. lia. }
assert (Hc64 : 0 <= c < 2 ^ 64) by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in Hcb; lia).
assert (BEVa : st_nev S2 + EV_ANSWER <= EV_MAX) by (unfold EV_REC_SHAPE_OF, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in *; lia).
assert (BLVa : blocks_bytes S2 + LIVE_ANSWER tA <= LIVE_MAX) by lia.
assert (MLE12 : mo_le MT S S2 (rec_spill_frees R * mo_free MT + XM_XSTRDUP MT x))
  by exact (mo_le_trans MT MTL _ _ _ _ _ HMLE MLE2).
assert (BMa : mo_ok MT S2 (XM_ANSWER MT tA)) by (apply (mok_station MT S S2 _ _ _ MTL HMOK' MLE12 XMA); lia).
(* 0x8d0c4: the tail jump into answer, which returns to descriptors_get's caller at answer's FP state fx1 *)
eapply SRr_mono.
{ eapply (cl_callS_wideF B LAWS W3 (ms_regs ms1) (ms_mem ms1) (Z_to_bv 64 (SIG CS_answer)) DESCRIPTORS_GET_STK (spZ regs)
    (dg_FP O) ly S W mem md [] ly2 S2 md5 _ ANSWER_STK
    ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) ::
      ablocks_fp (filter (fun pn => fst pn =? old) (lay_blocks QT)))
    EV_ANSWER 0 (getr regs 1) ch
    (fun ly' S' W' regs' mem' md' => exists p1 p2 O',
      let n := Z.of_nat (length tA) + 1 in
      getr regs' 10 = w64 p2 /\ 4096 <= p2 < 2 ^ 64 /\ p1 <> p2 /\
      (forall pn, In pn (ablocks B ly2 S2) -> fst pn <> old -> pn <> (p1, n) /\ pn <> (p2, n)) /\
      (forall pn, In pn (ablocks B ly' S') <-> (In pn (ablocks B ly2 S2) /\ fst pn <> old) \/ pn = (p1, n) \/ pn = (p2, n)) /\
      rec_repA B ly' S' (rdW W' mem') (fst (rec_answer RT (REC_DESCRIPTORS_GET, [x]) (shape_of dg_verb) false)) O' /\
      (forall pn, In pn O' <-> (In pn (lay_blocks QT) /\ fst pn <> old) \/ pn = (p1, n)) /\
      astr_atR (rdW W' mem') p2 tA /\
      blocks_bytes S' <= blocks_bytes S2 + LIVE_ANSWER tA /\
      mo_le MT S2 S' (XM_ANSWER MT tA)) HJ3 Psp);
  [ reflexivity | lia | vm_compute; congruence | rewrite HTS; vm_compute; congruence
  | exact P3' | exact P4' | exact Hraw | exact Hra | exact Hra4 | exact HchT
  | intros HPRE1; rewrite dg_sig_answer; eapply SRr_mono;
    [ exact (TANSWER fx ly2 S2 W3 (ms_regs ms1) (ms_mem ms1) md5 ch c q old (REC_DESCRIPTORS_GET, [x]) (shape_of dg_verb)
        false RT (lay_blocks QT) HPRE1 HFRM ltac:(rewrite HfrT; cbn [app]; exact Hfr8)
        HRODT HROT P10' Hc64 P11' Hq64 P12' HREPT Hold Hold64 (fun _ => conj HshT dg_fits)
        ltac:(intros _ Hf; discriminate Hf) BEVa BLVa BMa)
    | cbv beta; unfold apost_baseF;
      intros Wx cx _ (fx1 & lyx & Sx & regsx & memx & mdx & -> & Hf1 & Hf2 & HJ1 & HP & HK3);
      exists fx1, lyx, Sx, regsx, memx, mdx;
      split; [rewrite Hraw; reflexivity | split; [exact Hf1 | split; [exact Hf2 |
        split; [exact HJ1 | split; [exact HP | exact HK3]]]]] ]
  | intros a (r & Hr & Ha); destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha;
    [ apply dg_awr_grec; unfold A_G_REC, OFF_ANSWER, REC_SIZE in *; lia
    | apply dg_awr_grec; unfold A_G_REC, OFF_STATE, REC_SIZE in *; lia
    | unfold ablocks_fp in Hr; apply in_map_iff in Hr as ([b nb] & Er & Hin); subst r; cbn [fst snd] in Ha;
      apply dg_in_filter in Hin as [Hin Hb]; cbn [fst] in Hb;
      apply (Permutation_in _ HPQ) in Hin; apply in_app_iff in Hin as [Hin | [Hin | []]];
      [ right; left; split;
        [ exists (b, b + req_size nb); split;
          [ right; right; unfold ablocks_fp; apply in_map_iff; exists (b, nb); split; [reflexivity | exact (HQO _ Hin)]
          | cbn [fst snd]; lia ]
        | exists b, nb; split; [exact (HBLT _ Hin) | lia] ]
      | exfalso; injection Hin as Eb En; subst b nb; destruct Hold' as [Ho | (m & Hm)]; [lia|];
        apply Hpn; apply in_map_iff; exists (old, m); split; [cbn; lia | exact Hm] ] ]
  | intros lyx Sx Wx regsx memx mdx _ a (r & Hr & Ha) Hw _; exfalso;
    destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha;
    [ unfold A_G_REC, OFF_ANSWER in Ha; lia
    | unfold A_G_REC, OFF_STATE in Ha; lia
    | unfold ablocks_fp in Hr; apply in_map_iff in Hr as ([b nb] & Er & Hin); subst r; cbn [fst snd] in Ha;
      apply dg_in_filter in Hin as [Hin _]; apply (Permutation_in _ HPQ) in Hin;
      assert (Hin2 : In (b, nb) (ablocks B ly2 S2))
        by (apply in_app_iff in Hin as [Hin | [Hin | []]]; [exact (HBLT _ Hin) | rewrite <- Hin; exact Hpin2]);
      destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hin2) as (_ & _ & Hbc & _); lia ] ]. }
cbv beta. intros Wf cf _ (fx1 & lyf & Sf & regsf & memf & mdf & Hfx & -> & HJf & HJcf & HPf & HK).
destruct HK as (p1 & p2 & O' & HK). cbv zeta in HK.
destruct HK as (Hp2 & Hp2b & H12 & HGa & HLf & HRf & HO' & Hst2 & HBBf & MLEf).
pose proof (proj1 HJf) as HARf.
assert (H4096_2 : forall b, In b (ablocks B ly2 S2) -> 4096 <= fst b).
{ intros [b nb] Hb. destruct (al_blocks _ _ LAWS _ _ _ _ _ b nb HART Hb) as (_ & H4 & _). exact H4. }
destruct (dg_post_blocks (ablocks B ly S) (ablocks B lyc Sc) (ablocks B ly2 S2) (ablocks B lyf Sf) F (lay_blocks Qb)
  (lay_blocks QT) O O' p (LIVE_XSTRDUP x) p1 p2 (Z.of_nat (length tA) + 1) old
  HPF HFO HQO (fun pn H => proj1 (HKB pn H)) HOQ HPerm2 HFresh2 ltac:(unfold LIVE_XSTRDUP; lia) HPQ Hold'
  (fun b1 b2 H1 H2 He => dg_blocks_start ly2 S2 W3 (ms_mem ms1) md5 b1 b2 HART H1 H2 He)
  H4096_2 HGa H12 HLf HO'
  (fun b1 b2 H1 H2 He => dg_blocks_start lyf Sf Wf memf mdf b1 b2 HARf H1 H2 He)
  (fun b1 b2 H1 H2 Hne => dg_blocks_iv lyf Sf Wf memf mdf b1 b2 HARf H1 H2 Hne))
  as (B1 & B2 & B3 & B4 & B5).
(* answer returned at fx1 with fxrel fx fx1: that is descriptors_get's apost_baseF *)
apply (apost_baseF_intro (fx := fx) SEGS fx1 _ _ _ _ _ _ _ _ _ _ _ _ lyf Sf);
  [ exact Hfx
  | eapply (ajournal_mono_k SEGS B); [exact HJf | unfold EV_DESCRIPTORS_GET, EV_REC_SHAPE_OF in *; lia]
  | exact (aregs_preserved_trans _ _ _ HPRT HPf) |].
unfold dg_post.
exists (fst (rec_answer RT (REC_DESCRIPTORS_GET, [x]) (shape_of dg_verb) false)), tA, p2, O'.
split; [exact (surjective_pairing (rec_answer RT (REC_DESCRIPTORS_GET, [x]) (shape_of dg_verb) false))|].
split; [exact Hp2|]. split; [exact Hp2b|]. split; [exact HRf|]. split; [exact B1|].
split; [apply HLf; right; right; reflexivity|].
split; [exact B2|]. split; [exact B3|]. split; [exact Hst2|]. split; [exact B4|]. split; [exact B5|].
split.
- change (LIVE_DESCRIPTORS_GET R (Some x)) with (LIVE_XSTRDUP x + LIVE_ANSWER tA). lia.
- change (XM_DESCRIPTORS_GET MT R (Some x)) with (rec_spill_frees R * mo_free MT + XM_XSTRDUP MT x + XM_ANSWER MT tA).
  exact (mo_le_trans MT MTL _ _ _ _ _ MLE12 MLEf).
Qed.

End e.
End f.
End d.
