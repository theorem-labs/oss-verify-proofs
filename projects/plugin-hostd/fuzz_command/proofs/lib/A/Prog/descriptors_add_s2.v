(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the last segment of descriptors_add's ASan walk (plugin-hostd/fuzz_command),
   from the call of xstrdup to the return, after proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v (a segment through a
   program call and back, cl_callS and jafter_call_keep_pi) and lib/A/Prog/sup_reply_code.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaLibG PaLibH PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_free_c xstrdup_c mix_call_c descriptors_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas descriptors_add_s1 descriptors_add_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the registers at 0x8cedc and 0x8ceec: the frame below the caller's sp, the caller's gp/tp and s6..s11, s0 the
   slot, s1 the string, s2 = c + 4, s3 = g_rec, s4 the shadow base, s5 the shadow byte address of c + 4 *)
Definition da_regsM (regs regsc : bvmap 5 word) (c s : Z) : Prop :=
getr regsc 2 = Z_to_bv 64 (spZ regs - 64) /\ getr regsc 3 = getr regs 3 /\ getr regsc 4 = getr regs 4 /\
getr regsc 8 = Z_to_bv 64 c /\ getr regsc 9 = Z_to_bv 64 s /\ getr regsc 18 = Z_to_bv 64 (c + 4) /\
getr regsc 19 = Z_to_bv 64 A_G_REC /\ getr regsc 20 = Z_to_bv 64 DA_SB /\
getr regsc 21 = Z_to_bv 64 ((c + 4) / 8 + DA_SB) /\
(forall r, 22 <= r <= 27 -> getr regsc (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).

(* the registers at the join of record()'s two arms (0x8ceac): the frame below the caller's sp, the caller's gp/tp
   and s6..s11, s0 the slot, s1 the string pointer the caller passed, s3 = g_rec, s4 the shadow base *)
Definition da_regsJ (regs regsc : bvmap 5 word) (c pu : Z) : Prop :=
getr regsc 2 = Z_to_bv 64 (spZ regs - 64) /\ getr regsc 3 = getr regs 3 /\ getr regsc 4 = getr regs 4 /\
getr regsc 8 = Z_to_bv 64 c /\ getr regsc 9 = Z_to_bv 64 pu /\
getr regsc 19 = Z_to_bv 64 A_G_REC /\ getr regsc 20 = Z_to_bv 64 DA_SB /\
(forall r, 22 <= r <= 27 -> getr regsc (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).

(* after a run the model is `with_vm_backing (m_vm_lazy md) mat md` in the goal and the journal; name it, so a chain
   of runs does not double the term *)
Ltac da_fold_md :=
repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?mt ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) mt m) in *; clearbody mdv end.
(* the windows of a run of the walk's middle states: the frame is read-only, the slot's window its first 16 bytes,
   g_rec.state's its 8 bytes *)
Ltac da_win U8 U19 :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
intros a (r & Hin & Ha);
lazymatch type of Hin with In r ?rs => let rs' := eval vm_compute in rs in change rs with rs' in Hin end;
destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
[ lia | left; rewrite U8 in Ha; lia | right; rewrite U19 in Ha; unfold OFF_STATE in *; lia ].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
#[local] Notation LAWS := (AR_laws_ok SEGS B).
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis TMIX_CALL : forall fx0 : YK11.FPState, @tmix_call_spec fx0 rc SK PI B MT.
Hypothesis MTL : ameter_laws MT.
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
(* a live block's bytes up to the end of their 8-byte word are visible (a shared recorder-walk hypothesis; the
   statement's comment names it CmdRecFacts' cmd_heap_tail_vis): the tail word xstrdup's strlen reads *)
Hypothesis cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
In (p, n) (ablocks B ly S) -> p <= e < p + n -> atail_vis SEGS W mem e.
#[local] Set Default Proof Using "All".
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).

(* the post-condition of the statement (descriptors_add_c.v:90-99) *)
Definition da_Q (ly : alayout) (S : astate) (R : rstate) (uri : option (list byte)) (O : list (Z * Z))
: alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists O' : list (Z * Z),
 rec_repA B ly' S' (rdW W' mem') (descriptors_add_m R uri) O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O') /\
 blocks_bytes S' <= blocks_bytes S + LIVE_DESCRIPTORS_ADD uri /\
 mo_le MT S S' (XM_DESCRIPTORS_ADD MT R uri).

Lemma da_sig_xstrdup : SIG CS_xstrdup = BASE + AF_xstrdup.
Proof. rewrite (SIGP CS_xstrdup ltac:(vm_compute; repeat first [left; reflexivity | right])). reflexivity. Qed.
Lemma da_sig_mix_call : SIG CS_mix_call = BASE + AF_mix_call.
Proof. rewrite (SIGP CS_mix_call ltac:(vm_compute; repeat first [left; reflexivity | right])). reflexivity. Qed.
(* a callee with an empty footprint keeps the caller's frame (above its window) and every byte of the program's
   statics (image bytes no runtime entry owns): the journal's first and third clauses (lib/Reusable/YCbq.v:386-408) *)
Lemma da_call_kept : forall STK1 sp1 lyc Sc (Wc : world SEGS) memc mdc ly2 S2 (W2 : world SEGS) mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 [] lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
((sp1 <= a < 2 ^ 64 /\ alloc_ceiling <= a) \/ Exists (in_zr a) recb_PG) ->
aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a.
Proof.
intros STK1 sp1 lyc Sc Wc memc mdc ly2 S2 W2 mem2 md2 k1 a HJ Ha.
destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & K1 & _ & K3 & _).
assert (Hnf : ~ inFP [] a) by (intros (r & Hr & _); destruct Hr).
destruct Ha as [(Ha1 & Ha2) | HP].
- apply K1; [lia | lia | exact Hnf].
- assert (HP' : Exists (in_zr a) (as_prog_static B)) by (rewrite (ts_prog B HB); exact HP).
  destruct (prog_static_sep B a (ts_ok B HB) HP') as (H1 & H2 & _).
  apply K3; [exact (cmd_prog_img a HP) | exact H1 | exact H2 |].
  apply fp_spares_closed; [intros (r & Hr & _); destruct Hr | exact Hnf].
Qed.


(* a live block's bytes are no image bytes, so none of the program's statics *)
Lemma da_blk_not_PG : forall ly S (W : world SEGS) mem md q kk a, AR SEGS B ly S W mem md ->
In (q, kk) (ablocks B ly S) -> q <= a < q + req_size kk -> ~ Exists (in_zr a) recb_PG /\ 0 <= a < 2 ^ 64.
Proof.
intros ly S W mem md q kk a HAR Hin Ha.
destruct (al_blocks _ _ LAWS _ _ _ _ _ q kk HAR Hin) as (_ & H4096 & Hceil & _).
pose proof asan_consts as (C1 & _).
split; [|lia]. intros HP. apply (proj2 (al_client_img _ _ LAWS ly S W mem md a HAR
  (or_introl (ex_intro _ q (ex_intro _ kk (conj Hin Ha)))))). exact (cmd_prog_img a HP).
Qed.
(* the read-only range is off the footprint the statement names (g_rec, record.spill, the recorder's blocks) *)
Lemma da_ro_off_fp : forall ly S (W : world SEGS) mem md (O : list (Z * Z)) a, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> in_roP SEGS RLO RHI a -> ~ inFP (da_FP O) a.
Proof.
intros ly S W mem md O a HAR HO Hro (r & Hr & Ha). destruct (cmd_ro_prog_apart a Hro) as [Himg Hnp].
destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- exact (Hnp (recb_grec_in a Ha)).
- exact (Hnp (recb_spill_in a Ha)).
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([q kk] & <- & Hin). cbn [fst snd] in Ha.
  apply (proj2 (al_client_img _ _ LAWS ly S W mem md a HAR
    (or_introl (ex_intro _ q (ex_intro _ kk (conj (HO _ Hin) Ha)))))). exact Himg.
Qed.
(* arodata_okP along a journal of this call (CmdBase.v's arodata_ok_journalP) *)
Lemma da_aro_at : forall STK sp0 (O : list (Z * Z)) ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
ajournal SEGS B STK sp0 (da_FP O) ly S W mem md own ly' S' W' mem' md' k ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W' mem').
Proof.
intros STK sp0 O ly S W mem md own ly' S' W' mem' md' k HAR HO HJ HR.
eapply (arodata_ok_journalP (RO := RRO) SEGS RLO RHI RELRO_IMG B); [exact HJ | | exact HR].
intros a Hro. exact (da_ro_off_fp ly S W mem md O a HAR HO Hro).
Qed.
(* an own run of the walk writes only inside its windows, which lie in g_rec / record.spill *)
Lemma da_run_keeps : forall E rs (H : word -> bool) (m m' : word -> option byte),
frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, in_wrange E rs a -> Exists (in_zr a) recb_PG) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Exists (in_zr a) recb_PG -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' Hfr Hw a Ha Hn. apply (aview_eq_of SEGS). apply Hfr.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
intros Hin. exact (Hn (Hw a Hin)).
Qed.
Lemma da_tail_grows : forall (W : world SEGS) m m' e,
mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> atail_vis SEGS W m e -> atail_vis SEGS W m' e.
Proof.
intros W m m' e HG HT a Ha. specialize (HT a Ha). unfold aview, mbyte in *.
destruct (mrestrict (w_H W) m (Z_to_bv 64 a)) eqn:E1.
- pose proof (HG _ ltac:(rewrite E1; discriminate)) as H2.
  destruct (mrestrict (w_H W) m' (Z_to_bv 64 a)); [discriminate | contradiction].
- destruct (mrestrict (w_H W) m' (Z_to_bv 64 a)); [discriminate | exact HT].
Qed.
(* a string in a live heap block survives any change of memory outside the program's statics *)
Lemma da_heap_str_kept : forall ly S (W : world SEGS) mem md (rd' : reader) p x, AR SEGS B ly S W mem md ->
in_blockA (ablocks B ly S) p (Z.of_nat (length x) + 1) -> astr_atR (rdW W mem) p x ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Exists (in_zr a) recb_PG -> rd' a = rdW W mem a) ->
astr_atR rd' p x.
Proof.
intros ly S W mem md rd' p x HAR (q & kk & Hin & Hq1 & Hq2) Hstr HK.
apply (rastr_kept (rdW W mem)); [exact Hstr|]. intros i Hi.
pose proof (req_size_pos kk ltac:(destruct (al_blocks _ _ LAWS _ _ _ _ _ q kk HAR Hin) as (_ & _ & _ & _ & _ & _ & Hk); lia))
  as [_ Hrq].
destruct (da_blk_not_PG ly S W mem md q kk (p + i) HAR Hin ltac:(lia)) as [Hn Hr].
exact (HK (p + i) Hr Hn).
Qed.
(* the start of a live heap block is no null pointer *)
Lemma da_heap_pos : forall ly S (W : world SEGS) mem md p n, AR SEGS B ly S W mem md ->
in_blockA (ablocks B ly S) p n -> 4096 <= p.
Proof.
intros ly S W mem md p n HAR (q & kk & Hin & Hq1 & Hq2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ q kk HAR Hin) as (_ & H4096 & _). lia.
Qed.
(* the heap arm of astr_argA, with no recorder blocks to stay apart from (xstrdup's pre) *)
Lemma da_heap_arg : forall ly S rd p x, p <> 0 ->
in_blockA (ablocks B ly S) p (Z.of_nat (length x) + 1) -> astr_atR rd p x ->
Z.of_nat (length x) + 1 <= LMAX + 1 ->
astr_argA B ly S rd (in_roP SEGS RLO RHI) [] p (Some x).
Proof.
intros ly S rd p x Hp0 Hblk Hstr Hn. cbn zeta.
split; [exact Hp0|]. split; [exact Hstr|]. split; [exact Hn|].
left. split; [exact Hblk | apply Forall_nil].
Qed.

(* a byte off the program's statics is in no window of the walk *)
Lemma da_notPG_win : forall c a, da_slot_ok c -> ~ Exists (in_zr a) recb_PG ->
~ (c <= a < c + 16) /\ ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8).
Proof.
intros c a Hc Hn. split; intros Ha; apply Hn.
- destruct Hc as [(kk & Hkk & ->) | ->]; [apply recb_grec_in | apply recb_spill_in];
  unfold REC_CALLS_MAX, A_G_REC, A_REC_SPILL, OFF_CALLS, REC_SIZE, SC_SIZE, CALL_SIZE in *; lia.
- apply recb_grec_in. unfold A_G_REC, OFF_STATE, REC_SIZE in *. lia.
Qed.

(* PaDenot's field_of_region with the address and width as equations, so a walk can state them in its own form *)
Lemma da_field : forall E m n b cs lo hi wlo whi od (w : N) e v a k,
region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) -> a = b + od -> k = N.to_nat w ->
val_mem SEGS m a k v.
Proof.
intros E m n b cs lo hi wlo whi od w e v a k HR Hn Hc He Hv Hw -> ->.
exact (field_of_region E m n b cs lo hi wlo whi od w e v HR Hn Hc He Hv Hw).
Qed.
(* an own run keeps every byte outside its windows, here the slot's first 16 bytes and g_rec.state *)
Lemma da_keep_win : forall E rs (H : word -> bool) (m m' : word -> option byte) c,
frame_of E rs (mrestrict H m) (mrestrict H m') ->
(forall a, in_wrange E rs a -> (c <= a < c + 16) \/ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8)) ->
forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 16) -> ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8) ->
aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' c Hfr Hw a Ha Hn1 Hn2. apply (aview_eq_of SEGS). apply Hfr.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
intros Hin. destruct (Hw a Hin) as [H1 | H1]; [exact (Hn1 H1) | exact (Hn2 H1)].
Qed.
(* a callee with an empty footprint keeps the bytes of a block live before and after it *)
Lemma da_call_kept_blk : forall STK1 sp1 lyc Sc (Wc : world SEGS) memc mdc ly2 S2 (W2 : world SEGS) mem2 md2 k1 q kk i,
ajournal SEGS B STK1 sp1 [] lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
In (q, kk) (ablocks B lyc Sc) -> In (q, kk) (ablocks B ly2 S2) -> 0 <= i < req_size kk ->
aview SEGS (w_H W2) mem2 (q + i) = aview SEGS (w_H Wc) memc (q + i).
Proof.
intros STK1 sp1 lyc Sc Wc memc mdc ly2 S2 W2 mem2 md2 k1 q kk i HJ H1 H2 Hi.
destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & K2 & _).
apply (K2 q kk i H1 H2 Hi). intros (r & Hr & _); destruct Hr.
Qed.
(* the layout after the call names the layout's blocks and the copy (the spill slot's blocks are gone on the
   spill arm: record() freed them) *)
Lemma da_lay_in : forall Qb n pn q, ((16 <= n)%nat -> l_spill Qb = []) ->
In q (lay_blocks (lrf_lay Qb n pn)) <-> In q (lay_blocks Qb) \/ pn = q.
Proof.
intros Qb n pn q Hsp. unfold lrf_lay, lay_blocks.
destruct (Nat.ltb_spec n 16) as [Hn|Hn]; cbn [l_calls l_spill l_answer l_reply].
- rewrite List.concat_app. cbn [concat]. rewrite !in_app_iff. cbn [In]. tauto.
- rewrite (Hsp Hn). rewrite !in_app_iff. cbn [In]. tauto.
Qed.
(* a live block is apart from a range of the program's statics *)
Lemma da_apart_PG : forall ly S (W : world SEGS) mem md q kk b m, AR SEGS B ly S W mem md ->
In (q, kk) (ablocks B ly S) -> 1 <= kk -> 0 < m -> (forall a, b <= a < b + m -> Exists (in_zr a) recb_PG) ->
iv_apart q kk b m.
Proof.
intros ly S W mem md q kk b m HAR Hin Hk Hm HPG. unfold iv_apart.
destruct (Z_le_gt_dec (q + kk) b) as [H1|H1]; [left; exact H1|].
destruct (Z_le_gt_dec (b + m) q) as [H2|H2]; [right; exact H2|].
exfalso. pose proof (req_size_pos kk ltac:(lia)) as [_ Hrq].
destruct (da_blk_not_PG ly S W mem md q kk (Z.max q b) HAR Hin ltac:(lia)) as [Hn _].
apply Hn. apply HPG. lia.
Qed.
(* the post of the statement from the facts the walk ends with *)
Lemma da_post : forall ly S R uri O ly3 S3 (W3 : world SEGS) regs3 mem3 md3 bl0 rd0 Rb Qb c p x,
arep_at bl0 rd0 A_G_REC A_REC_SPILL Rb Qb ->
c = da_slot (Z.of_nat (length (r_calls Rb))) ->
((length (r_calls Rb) < 16)%nat ->
  aval_mem (rdW W3 mem3) (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls Rb)) + 1)) ->
((16 <= length (r_calls Rb))%nat -> snd (r_spill Rb) = []) ->
aval_mem (rdW W3 mem3) c 4 22 -> aval_mem (rdW W3 mem3) (c + 4) 4 1 -> aval_mem (rdW W3 mem3) (c + 8) 8 p ->
aval_mem (rdW W3 mem3) (A_G_REC + OFF_STATE) 8 (mixcall (r_state Rb) 22 [x]) ->
(forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
  ~ (c <= a < c + 16) -> ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8) ->
  ~ ((length (r_calls Rb) < 16)%nat /\ A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
  rdW W3 mem3 a = rd0 a) ->
(forall q kk i, In (q, kk) bl0 -> 0 <= i < kk -> rdW W3 mem3 (q + i) = rd0 (q + i)) ->
Permutation (ablocks B ly3 S3) ((p, LIVE_XSTRDUP x) :: bl0) ->
Forall (fun qk => iv_apart p (LIVE_XSTRDUP x) (fst qk) (snd qk)) bl0 ->
iv_apart p (LIVE_XSTRDUP x) A_G_REC REC_SIZE -> iv_apart p (LIVE_XSTRDUP x) A_REC_SPILL SC_SIZE ->
p <> 0 -> Z.of_nat (length x) <= LMAX -> astr_atR (rdW W3 mem3) p x ->
rec_mix (rec_record Rb 22 [x]) (22, [x]) = descriptors_add_m R uri ->
(forall pn, In pn (lay_blocks Qb) -> In pn O) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn bl0) ->
(forall pn, In pn bl0 -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn (lay_blocks Qb)) ->
blocks_bytes S3 <= blocks_bytes S + LIVE_DESCRIPTORS_ADD uri ->
mo_le MT S S3 (XM_DESCRIPTORS_ADD MT R uri) ->
da_Q ly S R uri O ly3 S3 W3 regs3 mem3 md3.
Proof.
intros ly S R uri O ly3 S3 W3 regs3 mem3 md3 bl0 rd0 Rb Qb c p x
  HA Hc HNC HSP Vfn Vna Varg Vst HK HKB HPerm HFr HapG HapS Hp0 Hx Hstr Hmodel HOb1 HOb2 HOb3 HBB HML.
assert (Hbl : forall pn, In pn bl0 -> In pn (ablocks B ly3 S3))
  by (intros pn Hin; apply (Permutation_in _ (Permutation_sym HPerm)); right; exact Hin).
assert (HinF : In (p, LIVE_XSTRDUP x) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym HPerm)); left; reflexivity).
assert (Hlc : lrf_c (Z.of_nat (length (r_calls Rb))) = c) by (rewrite Hc; reflexivity).
assert (Hspl : (16 <= length (r_calls Rb))%nat -> l_spill Qb = []).
{ intros Hn. pose proof HA as (_ & _ & _ & (_ & _ & _ & _ & HSPA & _) & _).
  destruct HSPA as (_ & _ & HlenS & _). rewrite (HSP Hn) in HlenS.
  destruct (l_spill Qb); [reflexivity | discriminate HlenS]. }
assert (Hnot : ~ In (p, LIVE_XSTRDUP x) bl0).
{ intros Hin. pose proof (proj1 (Forall_forall _ _) HFr _ Hin) as Hap. cbn [fst snd] in Hap.
  unfold iv_apart, LIVE_XSTRDUP in Hap. lia. }
assert (Hdec : forall a b : Z * Z, {a = b} + {a <> b}) by (decide equality; apply Z.eq_dec).
unfold da_Q. exists (lay_blocks (lrf_lay Qb (length (r_calls Rb)) (p, LIVE_XSTRDUP x))).
split; [|split; [|split; [|split; [|split]]]].
- unfold rec_repA. exists (lrf_lay Qb (length (r_calls Rb)) (p, LIVE_XSTRDUP x)). split; [|intros pn; reflexivity].
  rewrite <- Hmodel.
  eapply (lrf_rep_post bl0 (ablocks B ly3 S3) rd0 (rdW W3 mem3) Rb Qb 22 p (LIVE_XSTRDUP x) x HA HNC HSP);
  [ unfold REC_FN_COUNT; lia | rewrite Hlc; exact Vfn | rewrite Hlc; exact Vna | rewrite Hlc; exact Varg | exact Vst
  | intros a Ha H1 H2 H3; rewrite Hlc in H1; exact (HK a Ha H1 H2 H3) | exact HKB | exact Hbl | exact HinF
  | reflexivity | exact Hx | exact Hp0 | exact Hstr | exact HFr | exact HapG | exact HapS ].
- intros pn Hin. apply (da_lay_in Qb _ _ pn Hspl) in Hin as [Hin | <-]; [left; exact (HOb1 pn Hin)|].
  destruct (List.in_dec Hdec (p, LIVE_XSTRDUP x) (ablocks B ly S)) as [HinS | HnS]; [|right; exact HnS].
  destruct (List.in_dec Hdec (p, LIVE_XSTRDUP x) O) as [HinO | HnO]; [left; exact HinO|].
  exfalso. exact (Hnot (HOb2 _ HinS HnO)).
- intros pn HinS HnO. exact (Hbl pn (HOb2 pn HinS HnO)).
- intros pn Hin. apply (Permutation_in _ HPerm) in Hin. destruct Hin as [<- | Hin].
  + right. apply (da_lay_in Qb _ _ _ Hspl). right; reflexivity.
  + destruct (HOb3 pn Hin) as [H1 | H1]; [left; exact H1|].
    right. apply (da_lay_in Qb _ _ _ Hspl). left; exact H1.
- exact HBB.
- exact HML.
Qed.


Lemma da_segC : forall ly S W regs mem md ch R uri O lyc Sc Wc regsc memc mdc k
  (bl0 : list (Z * Z)) (rd0 : reader) (Rb : rstate) (Qb : rlay) (c s : Z) (x : list byte),
afn_pre SEGS B DESCRIPTORS_ADD_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
ajournal SEGS B DESCRIPTORS_ADD_STK (spZ regs) (da_FP O) ly S W mem md [] lyc Sc Wc memc mdc k ->
k = rec_spill_frees R ->
da_regsM regs regsc c s -> getr regsc 10 = Z_to_bv 64 s ->
da_frame_at (mrestrict (w_H Wc) memc) (spZ regs) regs ->
arep_at bl0 rd0 A_G_REC A_REC_SPILL Rb Qb -> ablocks B lyc Sc = bl0 ->
c = da_slot (Z.of_nat (length (r_calls Rb))) ->
((length (r_calls Rb) < 16)%nat ->
  aval_mem (rdW Wc memc) (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls Rb)) + 1)) ->
((16 <= length (r_calls Rb))%nat -> snd (r_spill Rb) = []) ->
aval_mem (rdW Wc memc) c 4 22 -> aval_mem (rdW Wc memc) (c + 4) 4 0 ->
(forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) -> ~ (c <= a < c + 8) ->
  ~ ((length (r_calls Rb) < 16)%nat /\ A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
  rdW Wc memc a = rd0 a) ->
(forall q kk i, In (q, kk) bl0 -> 0 <= i < kk -> rdW Wc memc (q + i) = rd0 (q + i)) ->
rec_mix (rec_record Rb 22 [x]) (22, [x]) = descriptors_add_m R uri ->
(forall pn, In pn (lay_blocks Qb) -> In pn O) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn bl0) ->
(forall pn, In pn bl0 -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn (lay_blocks Qb)) ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
mo_le MT S Sc (rec_spill_frees R * mo_free MT) -> mo_ok MT S (XM_DESCRIPTORS_ADD MT R uri) ->
st_nev S + EV_DESCRIPTORS_ADD R <= EV_MAX -> blocks_bytes Sc + LIVE_XSTRDUP x <= LIVE_MAX ->
x = sarg uri ->
in_blockA (ablocks B lyc Sc) s (Z.of_nat (length x) + 1) -> astr_atR (rdW Wc memc) s x ->
Z.of_nat (length x) + 1 <= LMAX + 1 ->
blocks_bytes Sc <= blocks_bytes S ->
SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + DA_CALL_XS)) memc (seg_rom SEGS)) mdc)
 (apost_base SEGS B DESCRIPTORS_ADD_STK (da_FP O) regs ly S W mem md (EV_DESCRIPTORS_ADD R) (da_Q ly S R uri O)).
Proof.
intros ly S W regs mem md ch R uri O lyc Sc Wc regsc memc mdc k bl0 rd0 Rb Qb c s x
  HPRE HROD HJ Hk HRG H10 Hfr HA0 Hbl0 Hc HNC1 HSP0 Hfn Hna HK HKB Hmodel HOb1 HOb2 HOb3 HO HML HMOK HEV HLIVE Hx
  HBLK HSTR HNL HBB0.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HTS : DESCRIPTORS_ADD_STK = 16560) by reflexivity.
pose proof (proj1 HJ) as HARc.
pose proof HRG as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22).
pose proof HA0 as (Hg8 & Hs8 & Hap & HC0 & HAN0 & HRP0 & HSC0 & HOWN0).
pose proof HC0 as (Hlen16 & HlenQ & Vnc0 & HCA0 & HSP0' & HSPL0).
pose proof HSC0 as (Vrf & Vcd & Vnr & Vst & Vho & Rrf & Rcd & Rnr & Rst & Rho).
assert (Hcok : da_slot_ok c) by (rewrite Hc; apply da_slot_okP; lia).
destruct (da_slot_bounds c Hcok) as (Hcb & Hc8 & Hcs).
assert (Hst : aval_mem (rdW Wc memc) (A_G_REC + OFF_STATE) 8 (r_state Rb)).
{ intros kk Hkk. rewrite HK; [exact (Vst kk Hkk) | left | | ]; unfold A_G_REC, OFF_STATE, REC_SIZE in *; [lia | | ].
  - destruct Hcs as [Hcs | ->]; unfold CALL_SIZE, A_REC_SPILL in *; lia.
  - unfold OFF_NCALLS. lia. }
assert (Hsp : bv_unsigned (getr regsc 2) = spZ regs - 64) by (rewrite R2; apply unsigned_lit_small; lia).
destruct (da_mid B TL HB VOBJS cmd_prog_img cmd_prog_writable lyc Sc Wc memc mdc regsc regs DA_CALL_XS (spZ regs) c (r_state Rb)
  HARc Hsp Hal16 ltac:(lia) Hfr R8 Hcok Hfn Hna R19 R20 R18 R21 Hst Rst) as [HS SHOK].
set (E := da_EM regsc regs (r_state Rb)) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold da_EM; apply Eimg_env).
assert (EL : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r).
{ intros n r Hn. subst E. unfold da_EM. pose proof (bv_unsigned_in_range 5 r) as Hr5.
  change (bv_modulus 5) with 32 in Hr5. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 64) by (rewrite (EL 2%nat 2%bv eq_refl); exact Hsp).
assert (U8 : bv_unsigned (ew E 8) = c)
  by (rewrite (EL 8%nat 8%bv eq_refl), R8; apply unsigned_lit_small; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
assert (U19 : bv_unsigned (ew E 19) = A_G_REC)
  by (rewrite (EL 19%nat 19%bv eq_refl), R19; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (EX : forall j, (j < 8)%nat -> ew E (32 + j) = nth j (da_extraM regs (r_state Rb)) (Z_to_bv 64 0)).
{ intros j Hj. subst E. unfold da_EM. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E39 : ew E 39 = Z_to_bv 64 (r_state Rb)) by (change 39%nat with (32 + 7)%nat; rewrite EX by lia; reflexivity).
paj_run_tok RUN HS HJ SHOK da_Bspan.
{ unfold ss_daM, da_rsM, da_frameM, da_slotM, da_stateM. cbn [ss_mem].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen with (n := 8%nat); [reflexivity | exact U8 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
    apply (da_awr_slot B TL HB VOBJS cmd_prog_img cmd_prog_writable _ _ _ _ _ _ _ _ c); [exact Hcok | unfold CALL_SIZE; lia]. }
  eapply awr_ok_cons_gen with (n := 19%nat); [reflexivity | exact U19 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
  apply (da_awr_grec B TL HB VOBJS cmd_prog_img cmd_prog_writable). unfold OFF_STATE, REC_SIZE in *. lia. }
da_fold_md. rename HFr into HFr1. rename HG into HG1. clear HF.
assert (KP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 16) -> ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8) ->
  aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a) by (apply (da_keep_win _ _ _ _ _ c HFr1); da_win U8 U19).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev1 & _).
(* 0x8ceec: the call of xstrdup on the string *)
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rg _ ?mm _; cfg_model := ?mdq |} _ =>
assert (Qsp : spZ rg = spZ regs + -64) by (unfold spZ at 1; rewrite Q2, Usp; lia);
assert (Q3' : getr rg 3 = w64 (as_gp B)) by (rewrite Q3, (EL 3%nat 3%bv eq_refl), R3; exact Hgp);
assert (Q4' : getr rg 4 = w64 (as_tp B)) by (rewrite Q4, (EL 4%nat 4%bv eq_refl), R4; exact Htp);
assert (Q10' : getr rg 10 = w64 s) by (rewrite Q10, (EL 10%nat 10%bv eq_refl), H10; reflexivity);
assert (Qs0 : achain lyc (aview SEGS (w_H Wc) mm) (spZ regs + -64) (s0Z rg) [])
  by (apply achain_low; unfold s0Z; rewrite Q8, (EL 8%nat 8%bv eq_refl), R8, unsigned_lit_small
      by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia); unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia);
eapply SRr_bind;
[ eapply (cl_callS B LAWS Wc rg mm _ DESCRIPTORS_ADD_STK (spZ regs) (da_FP O) ly S W mem md [] lyc Sc mdq k
    XSTRDUP_STK [] EV_XSTRDUP (-64) (getr rg 1) []
    (fun ly3 S3 W3 regs3 mem3 md3 => exists p : Z,
      getr regs3 10 = w64 p /\ 4096 <= p < 2 ^ 64 /\
      Permutation (ablocks B ly3 S3) ((p, LIVE_XSTRDUP x) :: ablocks B lyc Sc) /\
      Forall (fun qk => iv_apart p (LIVE_XSTRDUP x) (fst qk) (snd qk)) (ablocks B lyc Sc) /\
      in_blockA (ablocks B ly3 S3) p (LIVE_XSTRDUP x) /\
      astr_atR (rdW W3 mem3) p x /\ astr_atR (rdW W3 mem3) s x /\
      blocks_bytes S3 <= blocks_bytes Sc + LIVE_XSTRDUP x /\ mo_le MT Sc S3 (XM_XSTRDUP MT x)) HJ Qsp);
  [ reflexivity | lia | unfold XSTRDUP_STK, ASTACK; lia | rewrite HTS; unfold XSTRDUP_STK, ASTACK; lia
  | exact Q3' | exact Q4' | reflexivity | rewrite Q1; apply ret_ok_codeptr_v; [cbv; split; [congruence | reflexivity] | reflexivity]
  | rewrite Q1, unsigned_lit_small by lia; lia
  | exact Qs0
  | intros HPRE1; rewrite da_sig_xstrdup; eapply SRr_mono;
    [ eapply (TXSTRDUP fx lyc Sc Wc rg mm mdq [] s x HPRE1);
      [ exact (da_aro_at _ _ O ly S W mem md _ _ _ _ _ _ _ HAR HO HJ HROD) | exact Q10'
      | left; apply (da_heap_arg lyc Sc (rdW Wc mm) s x);
        [ pose proof (da_heap_pos lyc Sc Wc memc mdc s _ HARc HBLK); lia | exact HBLK
        | apply (da_heap_str_kept lyc Sc Wc memc mdc (rdW Wc mm) s x HARc HBLK HSTR);
          intros a Ha Hn; destruct (da_notPG_win c a Hcok Hn) as [N1 N2]; exact (KP1 a Ha N1 N2)
        | exact HNL ]
      | destruct HBLK as (q0 & k0 & Hin0 & Hq01 & Hq02);
        exact (cmd_heap_tail_vis lyc Sc Wc mm mdq q0 k0 (s + Z.of_nat (length x)) (proj1 HJ) Hin0 ltac:(lia))
      | rewrite Hk in Hnev1; unfold EV_DESCRIPTORS_ADD, EV_XSTRDUP in *; lia
      | exact HLIVE
      | apply (mok_station MT S Sc (XM_DESCRIPTORS_ADD MT R uri) (rec_spill_frees R * mo_free MT) (XM_XSTRDUP MT x) MTL HMOK HML);
        [ unfold XM_XSTRDUP; apply (mo_malloc_nonneg MT MTL); lia
        | unfold XM_DESCRIPTORS_ADD; rewrite Hx; lia ] ]
    | cbv beta; unfold apost_base; intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ1 & HP & HK3);
      exists ly3, S3, regs3, mem3, md3; split; [reflexivity | split; [exact HJ1 | split; [exact HP | exact HK3]]] ]
  | intros a (r & Hr & _); destruct Hr ]
| ] end.
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & p & Ha02 & Hp4096 & HPerm2 &
  HFresh2 & Hblk2 & Hpx2 & Hsx2 & HBB2 & MLE2).
(* back at 0x8cef0: the frame, the slot and g_rec.state are kept by xstrdup (its footprint is empty) *)
pose proof (proj1 HJ2) as HAR2.
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst].
  repeat apply Forall_cons; try apply Forall_nil; split;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha.
  - rewrite Usp in Ha. apply (mbyte_of_aview SEGS). apply (da_call_kept _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc2).
    left. split; [lia|]. rewrite HTS in Hslo. lia.
  - lia.
  - rewrite U8 in Ha. apply (mbyte_of_aview SEGS). apply (da_call_kept _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc2).
    right. destruct Hcok as [(kk & Hkk & ->) | ->]; [apply recb_grec_in | apply recb_spill_in];
    unfold REC_CALLS_MAX, A_G_REC, A_REC_SPILL, OFF_CALLS, REC_SIZE, SC_SIZE, CALL_SIZE in *; lia.
  - rewrite U8 in Ha. intros _. apply (cmd_prog_writable _ _ _ _ _ a HAR2).
    destruct Hcok as [(kk & Hkk & ->) | ->]; [apply recb_grec_in | apply recb_spill_in];
    unfold REC_CALLS_MAX, A_G_REC, A_REC_SPILL, OFF_CALLS, REC_SIZE, SC_SIZE, CALL_SIZE in *; lia.
  - rewrite U19 in Ha. apply (mbyte_of_aview SEGS). apply (da_call_kept _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc2).
    right. apply recb_grec_in. unfold A_G_REC, OFF_STATE, REC_SIZE in *. lia.
  - rewrite U19 in Ha. intros _. apply (cmd_prog_writable _ _ _ _ _ a HAR2).
    apply recb_grec_in. unfold A_G_REC, OFF_STATE, REC_SIZE in *. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS. rewrite Q1.
remember (havoc E 40 (map (getr regs2) CLOB)) as E2 eqn:HE2.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall n, (n < 40)%nat -> ew E2 n = ew E n) by (intros n Hn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hn).
assert (A44 : ew E2 44 = getr regs2 10) by (rewrite HE2; reflexivity).
assert (U8b : bv_unsigned (ew E2 8) = c) by (rewrite OLD2 by lia; exact U8).
assert (U19b : bv_unsigned (ew E2 19) = A_G_REC) by (rewrite OLD2 by lia; exact U19).
assert (SHOK2 : sh_ok SEGS da_BxM da_SHM E2 (mrestrict (w_H W2) mem2)).
{ apply (da_slot_sh_ok B TL HB VOBJS cmd_prog_img cmd_prog_writable ly2 S2 W2 mem2 md2 E2 8 20 c HAR2 Hcok).
  - rewrite OLD2, (EL 8%nat 8%bv eq_refl) by lia. exact R8.
  - rewrite OLD2, (EL 20%nat 20%bv eq_refl) by lia. exact R20. }
(* 0x8cef0 .. 0x8cf30: c->nargs := 1, c->args[0] := the copy, a0 := g_rec.state, a1 := c, and the call of mix_call *)
paj_run_tok RUN HS HJ2 SHOK2 da_Bspan.
{ lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen with (n := 8%nat); [reflexivity | exact U8b | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
    apply (da_awr_slot B TL HB VOBJS cmd_prog_img cmd_prog_writable _ _ _ _ _ _ _ _ c); [exact Hcok | unfold CALL_SIZE; lia]. }
  eapply awr_ok_cons_gen with (n := 19%nat); [reflexivity | exact U19b | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
  apply (da_awr_grec B TL HB VOBJS cmd_prog_img cmd_prog_writable). unfold OFF_STATE, REC_SIZE in *. lia. }
da_fold_md. rename HFr into HFr2. rename HG into HG2. clear HF.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnev2 & _).
assert (HinP2 : In (p, LIVE_XSTRDUP x) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym HPerm2)); left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p (LIVE_XSTRDUP x) HAR2 HinP2) as (_ & Hp4096' & Hpceil & _ & _ & _ & HpL).
pose proof (req_size_pos (LIVE_XSTRDUP x) ltac:(lia)) as [HreqL1 HreqL2].
pose proof HNL as HxL.
assert (Upa : sv_denot E2 (SOff 44 0) = Z_to_bv 64 p).
{ cbn [sv_denot]. rewrite A44, Ha02, unsigned_lit_small by lia. unfold w64. f_equal. lia. }
lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
  let r := eval vm_compute in (nth 1 (ss_mem ssx) da_frameM) in
  pose proof (st_ok_region_nth E2 ssx (restrict (w_H W2) msx) 1 r HS ltac:(vm_compute; reflexivity)) as HRs2;
  cbn [ms_mem restrict mkst] in HRs2;
  assert (KP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 16) -> ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8) ->
    aview SEGS (w_H W2) (ms_mem msx) a = aview SEGS (w_H W2) mem2 a)
    by (apply (da_keep_win _ _ _ _ _ c HFr2); da_win U8b U19b);
  assert (HCALL2 : acall_at (ablocks B ly2 S2) (rdW W2 (ms_mem msx)) c (22, [x]) [(p, LIVE_XSTRDUP x)])
end.
{ unfold acall_at. cbn [fst snd length].
  split; [unfold REC_FN_COUNT; lia|]. split; [lia|]. split; [reflexivity|].
  split; [apply (aval_mem_view SEGS);
    eapply (da_field E2 _ 8 c _ 0 56 0 16 0 4 (SLit 22) 22);
    [exact HRs2 | exact U8b | repeat (first [left; reflexivity | right]) | reflexivity
    | change (8 * Z.of_N 4) with 32; lia | change (Z.of_N 4) with 4; lia | unfold CALL_OFF_FN; lia | reflexivity]|].
  split; [apply (aval_mem_view SEGS);
    eapply (da_field E2 _ 8 c _ 0 56 0 16 4 4 (SLit 1) 1);
    [exact HRs2 | exact U8b | repeat (first [left; reflexivity | right]) | reflexivity
    | change (8 * Z.of_N 4) with 32; lia | change (Z.of_N 4) with 4; lia | unfold CALL_OFF_NARGS; lia | reflexivity]|].
  split; [cbn; apply NoDup_ListNoDup; apply List.NoDup_cons; [cbn; tauto | apply List.NoDup_nil]|].
  intros kk s0 pn Hs Hpn. destruct kk as [|kk]; [|destruct kk; discriminate Hs].
  cbn in Hs, Hpn. injection Hs as <-. injection Hpn as <-. cbn [fst snd].
  split; [apply (aval_mem_view SEGS);
    eapply (da_field E2 _ 8 c _ 0 56 0 16 8 8 (SOff 44 0) p);
    [exact HRs2 | exact U8b | repeat (first [left; reflexivity | right]) | exact Upa
    | change (8 * Z.of_N 8) with 64; lia | change (Z.of_N 8) with 8; lia | unfold CALL_OFF_ARGS; lia | reflexivity]|].
  split; [lia|]. split; [exact HinP2|]. split; [unfold LIVE_XSTRDUP, LMAX in *; lia|].
  apply (rastr_kept (rdW W2 mem2)); [exact Hpx2|]. intros i Hi.
  destruct (da_blk_not_PG ly2 S2 W2 mem2 md2 p (LIVE_XSTRDUP x) (p + i) HAR2 HinP2 ltac:(unfold LIVE_XSTRDUP in *; lia)) as [Hn1 Hn2].
  destruct (da_notPG_win c (p + i) Hcok Hn1) as [N1 N2]. exact (KP2 (p + i) Hn2 N1 N2). }
(* 0x8cf30: the call of mix_call on (g_rec.state, c) *)
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rg _ ?mm _; cfg_model := ?mdq |} _ =>
assert (Psp : spZ rg = spZ regs + -64) by (unfold spZ at 1; rewrite P2, OLD2, Usp by lia; lia);
assert (P3' : getr rg 3 = w64 (as_gp B)) by (rewrite P3, OLD2, (EL 3%nat 3%bv eq_refl), R3 by lia; exact Hgp);
assert (P4' : getr rg 4 = w64 (as_tp B)) by (rewrite P4, OLD2, (EL 4%nat 4%bv eq_refl), R4 by lia; exact Htp);
assert (P10' : getr rg 10 = w64 (r_state Rb)) by (rewrite P10, OLD2, E39 by lia; reflexivity);
assert (P11' : getr rg 11 = w64 c) by (rewrite P11, OLD2, (EL 8%nat 8%bv eq_refl), R8 by lia; reflexivity);
eapply SRr_bind;
[ eapply (cl_callS_na B LAWS W2 rg mm _ DESCRIPTORS_ADD_STK (spZ regs) (da_FP O) ly S W mem md [] ly2 S2 mdq _
    MIX_CALL_STK [] EV_MIX_CALL (-64) (getr rg 1)
    (fun ly3 S3 W3 regs3 mem3 md3 => getr regs3 10 = w64 (mixcall (r_state Rb) 22 [x]) /\
      Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) /\ ly3 = ly2 /\ S3 = S2) HJ2 Psp);
  [ reflexivity | lia | unfold MIX_CALL_STK, ESTACK; lia | rewrite HTS; unfold MIX_CALL_STK, ESTACK; lia
  | exact P3' | exact P4' | reflexivity | rewrite P1; apply ret_ok_codeptr_v; [cbv; split; [congruence | reflexivity] | reflexivity]
  | rewrite P1, unsigned_lit_small by lia; lia
  | intros HPRE2; rewrite da_sig_mix_call; eapply SRr_mono;
    [ eapply (TMIX_CALL fx ly2 S2 W2 rg mm mdq (r_state Rb) c (22, [x]) [(p, LIVE_XSTRDUP x)] HPRE2);
      [ exact (da_aro_at _ _ O ly S W mem md _ _ _ _ _ _ _ HAR HO HJ2 HROD) | exact P10' | exact Rst | exact P11'
      | exact Hcok | exact HCALL2
      | exact (cmd_ro_ok_of_aro ly2 S2 W2 mm _ (proj1 HJ2) (da_aro_at _ _ O ly S W mem md _ _ _ _ _ _ _ HAR HO HJ2 HROD))
      | rewrite Hk in Hnev2; unfold EV_MIX_CALL, EV_DESCRIPTORS_ADD, EV_XSTRDUP in *; lia ]
    | cbv beta; unfold apost_base; intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ1 & HP & HK4);
      exists ly4, S4, regs4, mem4, md4; split; [reflexivity | split; [exact HJ1 | split; [exact HP | exact HK4]]] ]
  | intros a (r & Hr & _); destruct Hr ]
| ] end.
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & Ha03 & HPerm3 & HlyE & HSE).
(* back at 0x8cf34 *)
pose proof (proj1 HJ3) as HAR3.
jafter_call_keep_pi HS 56%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0; 1; 2]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst].
  repeat apply Forall_cons; try apply Forall_nil; split;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite ?OLD2 in Ha by lia.
  - rewrite Usp in Ha. apply (mbyte_of_aview SEGS). apply (da_call_kept _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc3).
    left. split; [lia|]. rewrite HTS in Hslo. lia.
  - lia.
  - rewrite U8 in Ha. apply (mbyte_of_aview SEGS). apply (da_call_kept _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc3).
    right. destruct Hcok as [(kk & Hkk & ->) | ->]; [apply recb_grec_in | apply recb_spill_in];
    unfold REC_CALLS_MAX, A_G_REC, A_REC_SPILL, OFF_CALLS, REC_SIZE, SC_SIZE, CALL_SIZE in *; lia.
  - rewrite U8 in Ha. intros _. apply (cmd_prog_writable _ _ _ _ _ a HAR3).
    destruct Hcok as [(kk & Hkk & ->) | ->]; [apply recb_grec_in | apply recb_spill_in];
    unfold REC_CALLS_MAX, A_G_REC, A_REC_SPILL, OFF_CALLS, REC_SIZE, SC_SIZE, CALL_SIZE in *; lia.
  - rewrite U19 in Ha. apply (mbyte_of_aview SEGS). apply (da_call_kept _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc3).
    right. apply recb_grec_in. unfold A_G_REC, OFF_STATE, REC_SIZE in *. lia.
  - rewrite U19 in Ha. intros _. apply (cmd_prog_writable _ _ _ _ _ a HAR3).
    apply recb_grec_in. unfold A_G_REC, OFF_STATE, REC_SIZE in *. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS. rewrite P1.
remember (havoc E2 56 (map (getr regs3) CLOB)) as E3 eqn:HE3.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI2 | cbv; lia]).
assert (OLD3 : forall n, (n < 40)%nat -> ew E3 n = ew E n)
  by (intros n Hn; rewrite HE3, YN3v.ew_havoc_old by lia; apply OLD2; exact Hn).
assert (A60 : ew E3 60 = getr regs3 10) by (rewrite HE3; reflexivity).
assert (U19c : bv_unsigned (ew E3 19) = A_G_REC) by (rewrite OLD3 by lia; exact U19).
assert (SHOK3 : sh_ok SEGS da_BxM da_SHM E3 (mrestrict (w_H W3) mem3)).
{ apply (da_slot_sh_ok B TL HB VOBJS cmd_prog_img cmd_prog_writable ly3 S3 W3 mem3 md3 E3 8 20 c HAR3 Hcok).
  - rewrite OLD3, (EL 8%nat 8%bv eq_refl) by lia. exact R8.
  - rewrite OLD3, (EL 20%nat 20%bv eq_refl) by lia. exact R20. }
(* 0x8cf34 .. 0x8cf58: g_rec.state := the digest, the frame popped, ret *)
paj_run_tok RUN HS HJ3 SHOK3 da_Bspan.
{ lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen with (n := 8%nat); [reflexivity | rewrite OLD3 by lia; exact U8 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
    apply (da_awr_slot B TL HB VOBJS cmd_prog_img cmd_prog_writable _ _ _ _ _ _ _ _ c); [exact Hcok | unfold CALL_SIZE; lia]. }
  eapply awr_ok_cons_gen with (n := 19%nat); [reflexivity | exact U19c | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
  apply (da_awr_grec B TL HB VOBJS cmd_prog_img cmd_prog_writable). unfold OFF_STATE, REC_SIZE in *. lia. }
da_fold_md. rename HFr into HFr3. rename HG into HG3. clear HF.
assert (U8c : bv_unsigned (ew E3 8) = c) by (rewrite OLD3 by lia; exact U8).
lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
  let r := eval vm_compute in (nth 1 (ss_mem ssx) da_frameM) in
  pose proof (st_ok_pi_region_nth E3 ssx (restrict (w_H W3) msx) 1 r HS ltac:(vm_compute; reflexivity)) as HRs3;
  let r2 := eval vm_compute in (nth 2 (ss_mem ssx) da_frameM) in
  pose proof (st_ok_pi_region_nth E3 ssx (restrict (w_H W3) msx) 2 r2 HS ltac:(vm_compute; reflexivity)) as HRst3;
  cbn [ms_mem restrict mkst] in HRs3, HRst3;
  assert (KP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 16) -> ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8) ->
    aview SEGS (w_H W3) (ms_mem msx) a = aview SEGS (w_H W3) mem3 a)
    by (apply (da_keep_win _ _ _ _ _ c HFr3); da_win U8c U19c)
end.
(* what the end state keeps of the state at 0x8ceec *)
assert (HinP3 : In (p, LIVE_XSTRDUP x) (ablocks B ly3 S3)) by (apply (Permutation_in _ (Permutation_sym HPerm3)); exact HinP2).
assert (KPS : forall a, Exists (in_zr a) recb_PG -> ~ (c <= a < c + 16) -> ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8) ->
  rdW W3 (ms_mem ms1) a = rdW Wc memc a).
{ intros a HPa N1 N2.
  assert (Hr : 0 <= a < 2 ^ 64).
  { apply Exists_exists in HPa as ([b0 n0] & Hin & Hz). unfold in_zr in Hz. cbn [fst snd] in Hz.
    unfold recb_PG in Hin. destruct Hin as [Eq | [Eq | [Eq | []]]]; injection Eq as <- <-;
    unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE, A_G_QUITTING in Hz; lia. }
  rewrite (KP3 a Hr N1 N2), (da_call_kept _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc3 (or_intror HPa)), (KP2 a Hr N1 N2),
    (da_call_kept _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc2 (or_intror HPa)).
  exact (KP1 a Hr N1 N2). }
assert (KBL : forall q kk i, In (q, kk) bl0 -> 0 <= i < kk -> rdW W3 (ms_mem ms1) (q + i) = rdW Wc memc (q + i)).
{ intros q kk i Hin Hi. rewrite <- Hbl0 in Hin.
  assert (Hin2 : In (q, kk) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym HPerm2)); right; exact Hin).
  assert (Hin3 : In (q, kk) (ablocks B ly3 S3)) by (apply (Permutation_in _ (Permutation_sym HPerm3)); exact Hin2).
  pose proof (req_size_pos kk ltac:(lia)) as [_ Hrq].
  destruct (da_blk_not_PG lyc Sc Wc memc mdc q kk (q + i) HARc Hin ltac:(lia)) as [Hn Hr].
  destruct (da_notPG_win c (q + i) Hcok Hn) as [N1 N2].
  rewrite (KP3 _ Hr N1 N2), (da_call_kept_blk _ _ _ _ _ _ _ _ _ _ _ _ _ q kk i HJc3 Hin2 Hin3 ltac:(lia)),
    (KP2 _ Hr N1 N2), (da_call_kept_blk _ _ _ _ _ _ _ _ _ _ _ _ _ q kk i HJc2 Hin Hin2 ltac:(lia)).
  exact (KP1 _ Hr N1 N2). }
assert (KPp : forall i, 0 <= i < LIVE_XSTRDUP x -> rdW W3 (ms_mem ms1) (p + i) = rdW W2 mem2 (p + i)).
{ intros i Hi. pose proof (req_size_pos (LIVE_XSTRDUP x) ltac:(unfold LIVE_XSTRDUP in *; lia)) as [_ Hrq].
  destruct (da_blk_not_PG ly2 S2 W2 mem2 md2 p (LIVE_XSTRDUP x) (p + i) HAR2 HinP2 ltac:(lia)) as [Hn Hr].
  destruct (da_notPG_win c (p + i) Hcok Hn) as [N1 N2].
  rewrite (KP3 _ Hr N1 N2), (da_call_kept_blk _ _ _ _ _ _ _ _ _ _ _ _ _ p (LIVE_XSTRDUP x) i HJc3 HinP2 HinP3 ltac:(lia)).
  exact (KP2 _ Hr N1 N2). }
assert (MLE3 : mo_le MT S2 S3 0) by (rewrite HSE; exact (mo_le_refl MT MTL S2)).
(* 0x8cf58: ret to the caller, with the callee-saved registers restored from the frame *)
prreg HS (1%bv : bv 5) F1.
eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly3, S3, r, m, d end.
split.
{ rewrite F1, OLD3 by lia. change 32%nat with (32 + 0)%nat. rewrite EX by lia. cbn [da_extraM da_saved map app nth].
  replace (Z_to_bv 5 1) with (1%bv : bv 5) by (apply bv_eq; reflexivity).
  unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split.
{ apply (ajournal_materialize SEGS B LAWS Hsegs).
  replace (EV_DESCRIPTORS_ADD R) with (k + EV_XSTRDUP + EV_MIX_CALL) by (rewrite Hk; unfold EV_DESCRIPTORS_ADD, EV_MIX_CALL; lia).
  exact HJ3. }
split.
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
    r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  clear Hr.
  repeat (destruct Hr' as [-> | Hr']); [| | | | | | | | | | | | | | subst r];
  match goal with |- getr _ ?rr = _ => let X := fresh "X" in prreg HS rr X; rewrite X end;
  try (rewrite OLD3 by lia).
  - apply bv_eq. rewrite Z_to_bv_unsigned, Usp.
    replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). fold (spZ regs).
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small; lia.
  - rewrite (EL 3%nat (Z_to_bv 5 3) eq_refl).
    replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). exact R3.
  - rewrite (EL 4%nat (Z_to_bv 5 4) eq_refl).
    replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). exact R4.
  - change 33%nat with (32 + 1)%nat. rewrite EX by lia. reflexivity.
  - change 34%nat with (32 + 2)%nat. rewrite EX by lia. reflexivity.
  - change 35%nat with (32 + 3)%nat. rewrite EX by lia. reflexivity.
  - change 36%nat with (32 + 4)%nat. rewrite EX by lia. reflexivity.
  - change 37%nat with (32 + 5)%nat. rewrite EX by lia. reflexivity.
  - change 38%nat with (32 + 6)%nat. rewrite EX by lia. reflexivity.
  - rewrite (EL 22%nat (Z_to_bv 5 22) eq_refl). apply R22. lia.
  - rewrite (EL 23%nat (Z_to_bv 5 23) eq_refl). apply R22. lia.
  - rewrite (EL 24%nat (Z_to_bv 5 24) eq_refl). apply R22. lia.
  - rewrite (EL 25%nat (Z_to_bv 5 25) eq_refl). apply R22. lia.
  - rewrite (EL 26%nat (Z_to_bv 5 26) eq_refl). apply R22. lia.
  - rewrite (EL 27%nat (Z_to_bv 5 27) eq_refl). apply R22. lia. }
(* the post *)
assert (Hn16 : (Z.of_nat (length (r_calls Rb)) <= 16)) by lia.
pose proof (mixcall_range (r_state Rb) 22 [x] Rst) as Hmr.
eapply (da_post ly S R uri O ly3 S3 W3 _ _ _ bl0 rd0 Rb Qb c p x HA0 Hc).
- intros Hlt k0 Hk0. rewrite (KPS (A_G_REC + OFF_NCALLS + Z.of_nat k0)).
  + exact (HNC1 Hlt k0 Hk0).
  + apply recb_grec_in. unfold A_G_REC, OFF_NCALLS, REC_SIZE in *. lia.
  + rewrite Hc. unfold da_slot. destruct (Z.eqb_spec (Z.of_nat (length (r_calls Rb))) 16); [lia|].
    unfold A_G_REC, OFF_CALLS, OFF_NCALLS, CALL_SIZE in *. lia.
  + unfold A_G_REC, OFF_STATE, OFF_NCALLS in *. lia.
- exact HSP0.
- apply (aval_mem_view SEGS). eapply (da_field E3 _ 8 c _ 0 56 0 16 0 4 (SLit 22) 22);
  [exact HRs3 | exact U8c | repeat (first [left; reflexivity | right]) | reflexivity
  | change (8 * Z.of_N 4) with 32; lia | change (Z.of_N 4) with 4; lia | lia | reflexivity].
- apply (aval_mem_view SEGS). eapply (da_field E3 _ 8 c _ 0 56 0 16 4 4 (SLit 1) 1);
  [exact HRs3 | exact U8c | repeat (first [left; reflexivity | right]) | reflexivity
  | change (8 * Z.of_N 4) with 32; lia | change (Z.of_N 4) with 4; lia | lia | reflexivity].
- apply (aval_mem_view SEGS). eapply (da_field E3 _ 8 c _ 0 56 0 16 8 8 (SOff 44 0) p);
  [exact HRs3 | exact U8c | repeat (first [left; reflexivity | right]) |
  | change (8 * Z.of_N 8) with 64; lia | change (Z.of_N 8) with 8; lia | lia | reflexivity].
  cbn [sv_denot]. rewrite HE3, YN3v.ew_havoc_old by lia. rewrite A44, Ha02, unsigned_lit_small by lia.
  unfold w64. f_equal. lia.
- apply (aval_mem_view SEGS). eapply (da_field E3 _ 19 A_G_REC _ OFF_STATE (OFF_STATE + 8) OFF_STATE (OFF_STATE + 8)
    OFF_STATE 8 (SOff 60 0) (mixcall (r_state Rb) 22 [x]));
  [exact HRst3 | exact U19c | left; reflexivity |
  | change (8 * Z.of_N 8) with 64; lia | change (Z.of_N 8) with 8; lia | lia | reflexivity].
  cbn [sv_denot]. rewrite A60, Ha03, unsigned_lit_small by lia. unfold w64. f_equal. lia.
- intros a Ha N1 N2 N3. rewrite (KPS a ltac:(destruct Ha; [apply recb_grec_in | apply recb_spill_in]; lia) N1 N2).
  apply HK; [exact Ha | lia | exact N3].
- intros q kk i Hin Hi. rewrite (KBL q kk i Hin Hi). exact (HKB q kk i Hin Hi).
- rewrite <- Hbl0. exact (perm_trans HPerm3 HPerm2).
- rewrite <- Hbl0. exact HFresh2.
- apply (da_apart_PG ly2 S2 W2 mem2 md2 p _ A_G_REC REC_SIZE HAR2 HinP2); [unfold LIVE_XSTRDUP; lia | unfold REC_SIZE; lia |].
  intros a Ha. apply recb_grec_in. exact Ha.
- apply (da_apart_PG ly2 S2 W2 mem2 md2 p _ A_REC_SPILL SC_SIZE HAR2 HinP2); [unfold LIVE_XSTRDUP; lia | unfold SC_SIZE; lia |].
  intros a Ha. apply recb_spill_in. exact Ha.
- lia.
- lia.
- apply (rastr_kept (rdW W2 mem2)); [exact Hpx2|]. intros i Hi. apply KPp. unfold LIVE_XSTRDUP. exact Hi.
- exact Hmodel.
- exact HOb1.
- exact HOb2.
- exact HOb3.
- rewrite HSE. unfold LIVE_DESCRIPTORS_ADD. rewrite <- Hx. lia.
- pose proof (mo_le_trans MT MTL _ _ _ _ _ HML MLE2) as M1.
  pose proof (mo_le_trans MT MTL _ _ _ _ _ M1 MLE3) as M2.
  apply (mo_le_mono MT MTL _ _ _ _ M2). unfold XM_DESCRIPTORS_ADD. rewrite <- Hx. lia.
Qed.

(* the walk from the join of record()'s two arms (0x8ceac) to the return, as each arm hands it over: the state at
   the join (Sc, the recorder Rb / Qb at the reader rd0 that record() left), what the arm kept of it, and the
   string argument at the join, a string in a live heap block (the statement's form, descriptors_add_c.v:79-82) *)
Definition da_join_K (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (R : rstate) (uri : option (list byte)) (O : list (Z * Z)) (pu : Z) : Prop :=
forall lyc Sc (Wc : world SEGS) (regsc : bvmap 5 word) memc mdc k (bl0 : list (Z * Z)) (rd0 : reader)
  (Rb : rstate) (Qb : rlay) (c : Z),
ajournal SEGS B DESCRIPTORS_ADD_STK (spZ regs) (da_FP O) ly S W mem md [] lyc Sc Wc memc mdc k ->
k = rec_spill_frees R ->
da_regsJ regs regsc c pu ->
da_frame_at (mrestrict (w_H Wc) memc) (spZ regs) regs ->
arep_at bl0 rd0 A_G_REC A_REC_SPILL Rb Qb -> ablocks B lyc Sc = bl0 ->
c = da_slot (Z.of_nat (length (r_calls Rb))) ->
((length (r_calls Rb) < 16)%nat ->
  aval_mem (rdW Wc memc) (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls Rb)) + 1)) ->
((16 <= length (r_calls Rb))%nat -> snd (r_spill Rb) = []) ->
(forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
  ~ ((length (r_calls Rb) < 16)%nat /\ A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
  rdW Wc memc a = rd0 a) ->
(forall q kk i, In (q, kk) bl0 -> 0 <= i < kk -> rdW Wc memc (q + i) = rd0 (q + i)) ->
rec_mix (rec_record Rb 22 [sarg uri]) (22, [sarg uri]) = descriptors_add_m R uri ->
(forall pn, In pn (lay_blocks Qb) -> In pn O) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn bl0) ->
(forall pn, In pn bl0 -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn (lay_blocks Qb)) ->
mo_le MT S Sc (rec_spill_frees R * mo_free MT) ->
blocks_bytes Sc <= blocks_bytes S ->
(exists x, uri = Some x /\
 in_blockA (ablocks B lyc Sc) pu (Z.of_nat (length x) + 1) /\ astr_atR (rdW Wc memc) pu x /\
 Z.of_nat (length x) + 1 <= LMAX + 1) ->
SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + DA_JOIN)) memc (seg_rom SEGS)) mdc)
 (apost_base SEGS B DESCRIPTORS_ADD_STK (da_FP O) regs ly S W mem md (EV_DESCRIPTORS_ADD R) (da_Q ly S R uri O)).

End e.
End f.
End d.
