(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the kit of the entry segment of answer's ASan+UBSan walk (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan, 0x8aa10 .. 0x8ab6c): the walk tactics answer_s1.v does not carry (as sup_resp's walk lane
   carried them over from cgif lib/A/ACkc.v), the symbolic entry state and its seed (cgif's flushFrame seed,
   lib/A/ACj0.v, as sup_resp's sr_entry), and the recorder's representation carried over a step that keeps the
   recorder's bytes. The B twin of lib/A/Prog/answer_e1.v (a working branch d28426fbb96) with the B kit's module
   paths (lib/B, lib/B/Prog, lib/B/Rt): B's entry code is A's instruction for instruction, and the objects the seed
   names (A_OBJ 0, the shadow-base GOT word 0xa5f50; A_OBJ 1, the use-after-return GOT word 0xa5fa8; A_OBJ 12, the
   shadow cell 0xb0c38) are A's slots. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtStack RtShadow RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import mix_call_c hand_back_c answer_c PaFx answer_s0 answer_s1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the walk tactics answer_s1.v does not carry (sup_resp's walk lane's copies of cgif lib/A/ACkc.v) ---- *)
Ltac rebaseE HS AG HEv :=
let AG2 := fresh "AG" in let Ev := fresh "E" in
lazymatch type of AG with forall n, _ -> _ = ew ?E0 n =>
lazymatch type of HS with st_ok_pi _ _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
let HEIv := fresh "HEI" in
lazymatch type of HEv with
| _ = havoc ?Eo ?kk ?ws => lazymatch goal with Ho : img_env ?val ?lim Eo |- _ =>
first [ pose proof (img_env_havoc_hi Eo kk ws Ho ltac:(cbv; lia)) as HEIv | pose proof (img_env_havoc Eo kk ws Ho ltac:(cbv; lia)) as HEIv ];
rewrite <- HEv in HEIv end
| _ = ?En => try (lazymatch goal with Hn : img_env _ _ En |- _ => rewrite <- HEv in Hn end) end;
repeat match goal with H : img_env _ _ (ewset _ _ _) |- _ => clear H end;
assert (AG2 : forall n, (n < 32)%nat -> ew Ev n = ew E0 n)
by (intros nn Hnn; rewrite HEv; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; apply AG; exact Hnn);
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| _ => lazymatch (eval cbv in (Nat.leb 32 n)) with
| true => let H2 := fresh H in
assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ?ew_ewset_other, ?ew_havoc_old, ?ew_havoc_above by nat_side; rewrite ?ew_ewset_other, ?ew_havoc_old, ?ew_havoc_above by nat_side; exact H);
clear H; rename H2 into H
end end end;
clear AG; rename AG2 into AG end end.
Ltac rreg_by HS r v pf H :=
lazymatch type of HS with st_ok_pi _ ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (H : getr rg r = v) by (refine (eq_trans (st_ok_restrict_reg _ Hh Ex _ ms r HS) _); change (sv_denot Ex e = v); exact pf) | st_ok ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (H : getr rg r = v) by (refine (eq_trans (st_ok_restrict_reg segs Hh Ex ss ms r HS) _); change (sv_denot Ex e = v); exact pf) end.
Ltac norm_ssp HS := lazymatch type of HS with
| st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS
| st_ok _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
(* the model after a run: name it, so that the next run does not nest it (WalkAnswer2, 2026-10-28) *)
Ltac mdv_name := try (let mdv := fresh "mdv" in set (mdv := with_vm_backing _ _ _) in *; clearbody mdv).

(* ---- answer's entry state ---- *)
(* the walk makes no inline check before BODY, so its shadow entry list stays empty *)
Definition AN_Bx : sv := SOff 32 0.
Definition AN_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Ltac resh HS :=
try match goal with H : sh_ok _ _ _ _ _ |- _ => clear H end;
lazymatch type of HS with st_ok_pi ?sg _ ?Ex _ (restrict (w_H ?Wx) ?msx) =>
let SH := fresh "SHOK" in
assert (SH : sh_ok sg AN_Bx [] Ex (mrestrict (w_H Wx) (ms_mem msx))) by (unfold sh_ok; apply Forall_nil) end.
(* the 128-byte frame below the entry sp, the shadow GOT word and cell, the use-after-return GOT word and flag *)
Definition an_regions0 : smem :=
[ stack_region 128; got_regionP; bcell_regionP 32; uar_got_regionP 33; uar_cell_regionP 33 ].
Definition an_atoms0 : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0); (33%nat, mkAF 0x10000 0x606000 2) ].
Definition ss_an0 : sstate := mkSS AF_answer sr_atoms an_regions0 None (mkFacts an_atoms0 [] []).
Definition an_extra (uar : Z) : list word := map (Z_to_bv 64) [SB; uar].

(* ---- the recorder's bytes: g_rec and record.spill, and the live blocks ---- *)
Definition in_rec (a : Z) : Prop :=
A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE.
Definition rk_set (bl : list (Z * Z)) (a : Z) : Prop :=
in_rec a \/ exists p n, In (p, n) bl /\ p <= a < p + n.
Definition rkeep (bl : list (Z * Z)) (rd rd' : reader) : Prop :=
forall a, rk_set bl a -> rd' a = rd a.
Lemma rkeep_refl : forall bl rd, rkeep bl rd rd.
Proof. intros bl rd a _. reflexivity. Qed.
Lemma rkeep_trans : forall bl rd1 rd2 rd3, rkeep bl rd1 rd2 -> rkeep bl rd2 rd3 -> rkeep bl rd1 rd3.
Proof. intros bl rd1 rd2 rd3 H12 H23 a Ha. rewrite (H23 a Ha). exact (H12 a Ha). Qed.
Lemma aval_mem_kept_on : forall (rd rd' : reader) a n v,
aval_mem rd a n v -> (forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk k Hlt. rewrite (Hk k Hlt). exact (H k Hlt). Qed.
Lemma abytes_atR_kept_on : forall (rd rd' : reader) p l,
abytes_atR rd p l -> (forall i, 0 <= i < Z.of_nat (length l) -> rd' (p + i) = rd (p + i)) -> abytes_atR rd' p l.
Proof. intros rd rd' p l H Hk i Hi. rewrite (Hk (Z.of_nat i)) by lia. exact (H i Hi). Qed.
Lemma astr_atR_kept_on : forall (rd rd' : reader) p s,
astr_atR rd p s -> (forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (p + i) = rd (p + i)) -> astr_atR rd' p s.
Proof.
intros rd rd' p s [H1 H2] Hk. split; [|exact H2]. apply (abytes_atR_kept_on rd rd' p _ H1).
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Hk. lia.
Qed.
Lemma nth_error_lt : forall {A} (l : list A) i x, nth_error l i = Some x -> (i < length l)%nat.
Proof. intros A l i x H. apply nth_error_Some. rewrite H. discriminate. Qed.
(* a step that keeps the recorder's bytes and the bytes of the live blocks keeps its representation *)
Lemma rec_repA_kept : forall B ly S ly' S' (rd rd' : reader) R O,
rec_repA B ly S rd R O -> rkeep (ablocks B ly S) rd rd' -> ablocks B ly' S' = ablocks B ly S ->
rec_repA B ly' S' rd' R O.
Proof.
intros B ly S ly' S' rd rd' R O (Q & HA & HO) HK Eab. exists Q. split; [|exact HO]. rewrite Eab.
set (bl := ablocks B ly S) in *.
assert (KR : forall a, in_rec a -> rd' a = rd a) by (intros a Ha; apply HK; left; exact Ha).
assert (KB : forall p n i, In (p, n) bl -> 0 <= i < n -> rd' (p + i) = rd (p + i))
by (intros p n i Hin Hi; apply HK; right; exists p, n; split; [exact Hin | lia]).
assert (KV : forall a n v, (forall k, (k < n)%nat -> in_rec (a + Z.of_nat k)) -> aval_mem rd a n v -> aval_mem rd' a n v)
by (intros a n v Hr Hv; apply (aval_mem_kept_on rd rd' a n v Hv); intros k Hk; apply KR, Hr, Hk).
assert (KT : forall pn s, In pn bl -> Z.of_nat (length s) + 1 <= snd pn -> astr_atR rd (fst pn) s -> astr_atR rd' (fst pn) s).
{ intros [p n] s Hin Hl Hs. cbn [fst snd] in *. apply (astr_atR_kept_on rd rd' p s Hs). intros i Hi. apply (KB p n i Hin). lia. }
assert (KY : forall pn l, In pn bl -> Z.of_nat (length l) <= snd pn -> abytes_atR rd (fst pn) l -> abytes_atR rd' (fst pn) l).
{ intros [p n] l Hin Hl Hs. cbn [fst snd] in *. apply (abytes_atR_kept_on rd rd' p l Hs). intros i Hi. apply (KB p n i Hin). lia. }
assert (KC : forall a c P, (forall o, 0 <= o < CALL_SIZE -> in_rec (a + o)) -> acall_at bl rd a c P -> acall_at bl rd' a c P).
{ intros a c P Ha (C1 & C2 & C3 & C4 & C5 & C6 & C7). unfold acall_at.
  split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
  split; [apply KV; [intros k Hk; rewrite <- Z.add_assoc; apply Ha; unfold CALL_OFF_FN, CALL_SIZE; lia | exact C4]|].
  split; [apply KV; [intros k Hk; rewrite <- Z.add_assoc; apply Ha; unfold CALL_OFF_NARGS, CALL_SIZE; lia | exact C5]|].
  split; [exact C6|].
  intros k s pn Hs Hp. destruct (C7 k s pn Hs Hp) as (D1 & D2 & D3 & D4 & D5).
  assert (Hk6 : (k < 6)%nat) by (pose proof (nth_error_lt _ _ _ Hs); lia).
  split; [apply KV; [intros j Hj; rewrite <- !Z.add_assoc; apply Ha; unfold CALL_OFF_ARGS, CALL_SIZE; lia | exact D1]|].
  split; [exact D2|]. split; [exact D3|]. split; [exact D4|]. exact (KT pn s D3 ltac:(lia) D5). }
destruct HA as (Hg8 & Hs8 & Hap & HC & HAn & HRp & HSc & HOwn).
unfold arep_at. split; [exact Hg8|]. split; [exact Hs8|]. split; [exact Hap|].
split.
{ destruct HC as (C1 & C2 & C3 & C4 & C5 & C6). split; [exact C1|]. split; [exact C2|].
  split; [apply KV; [intros k Hk; left; unfold A_G_REC, OFF_NCALLS, REC_SIZE; lia | exact C3]|].
  split.
  - intros i c P Hc HP. destruct (C4 i c P Hc HP) as [D1 D2]. split; [|exact D2].
    assert (Hi : (i < 16)%nat) by (pose proof (nth_error_lt _ _ _ Hc); lia).
    apply KC; [|exact D1]. intros o Ho. left. unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
  - split; [|exact C6]. apply KC; [|exact C5]. intros o Ho. right. unfold A_REC_SPILL, CALL_SIZE, SC_SIZE in *. lia. }
split.
{ unfold aanswer_at in *. destruct (r_answer R) as [x|]; destruct (l_answer Q) as [pn|]; try exact HAn.
  - destruct HAn as (A1 & A2 & A3 & A4 & A5 & A6).
    split; [apply KV; [intros k Hk; left; unfold A_G_REC, OFF_ANSWER, REC_SIZE; lia | exact A1]|].
    split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact (KT pn x A3 ltac:(lia) A5) | exact A6].
  - apply KV; [intros k Hk; left; unfold A_G_REC, OFF_ANSWER, REC_SIZE; lia | exact HAn]. }
split.
{ unfold areply_at in *. destruct (r_reply R) as [x|]; destruct (l_reply Q) as [pn|]; try exact HRp.
  - destruct HRp as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    split; [apply KV; [intros k Hk; left; unfold A_G_REC, OFF_REPLY, REC_SIZE; lia | exact A1]|].
    split; [apply KV; [intros k Hk; left; unfold A_G_REC, OFF_REPLY_SIZE, REC_SIZE; lia | exact A2]|].
    split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|].
    split; [exact (KY pn x A5 ltac:(lia) A7) | exact A8].
  - destruct HRp as [A1 A2].
    split; [apply KV; [intros k Hk; left; unfold A_G_REC, OFF_REPLY, REC_SIZE; lia | exact A1]|].
    apply KV; [intros k Hk; left; unfold A_G_REC, OFF_REPLY_SIZE, REC_SIZE; lia | exact A2]. }
split; [|exact HOwn].
destruct HSc as (S1 & S2 & S3 & S4 & S5 & S6).
split; [apply KV; [intros k Hk; left; unfold A_G_REC, OFF_REFUSE, REC_SIZE; lia | exact S1]|].
split; [apply KV; [intros k Hk; left; unfold A_G_REC, OFF_CODE, REC_SIZE; lia | exact S2]|].
split; [apply KV; [intros k Hk; left; unfold A_G_REC, OFF_NREPLIES, REC_SIZE; lia | exact S3]|].
split; [apply KV; [intros k Hk; left; unfold A_G_REC, OFF_STATE, REC_SIZE; lia | exact S4]|].
split; [apply KV; [intros k Hk; left; unfold A_G_REC, OFF_HOST, REC_SIZE; lia | exact S5]|].
exact S6.
Qed.
Lemma aval_mem_rkeep : forall bl (rd rd' : reader) a n v,
rkeep bl rd rd' -> (forall k, (k < n)%nat -> in_rec (a + Z.of_nat k)) -> aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros bl rd rd' a n v HK Hr Hv. apply (aval_mem_kept_on rd rd' a n v Hv). intros k Hk. apply HK. left. exact (Hr k Hk). Qed.
(* a value the symbolic memory holds is a value the reader shows *)
Lemma aval_mem_of_val_mem : forall segs H mem a n v,
val_mem segs (mrestrict H mem) a n v -> aval_mem (aview segs H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold YO0f.le_byte, le_byte. apply Z.mod_mod. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* a run keeps the recorder's bytes when its windows lie in a set Zs those bytes miss *)
Lemma rkeep_of_frame : forall segs E rs H (m m' : word -> option byte) (Zs : Z -> Prop) bl,
frame_of E rs (mrestrict H m) (mrestrict H m') ->
(forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> Zs a) ->
(forall a, rk_set bl a -> 0 <= a < 2 ^ 64 /\ ~ Zs a) ->
rkeep bl (aview segs H m) (aview segs H m').
Proof.
intros segs E rs H m m' Zs bl HF Hw Hn a Ha. destruct (Hn a Ha) as [Hr HZ].
exact (kept_of_frame (segs:=segs) E rs H m m' Zs HF Hw a Hr HZ).
Qed.
Section b.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section c.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib (PI := PI) B.
Hypothesis TLF : PALibF (PI := PI) B.
(* the seed: sup_resp's sr_entry (cgif's flushFrame seed) with answer's 128-byte frame *)
Lemma an_entry_st : forall W ly S regs mem md ch,
afn_pre SEGS B ANSWER_STK ly S W regs mem md ch ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (an_extra (as_uar_cell B)))) ss_an0
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_answer)) mem (seg_rom SEGS))).
Proof.
intros W ly S regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : ANSWER_STK = 16592) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell. rewrite (palf_got_uar B TLF) in Kguar.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (an_extra (as_uar_cell B)))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1. pose proof (pa_obj_img 12 ltac:(lia)) as Hob12.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold ss_an0. apply (pa_entry_st_ok_full (PI := PI)).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold an_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
repeat apply Forall_cons; try apply Forall_nil.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
  split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
  [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
  rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
  [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
  rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 33 0) (as_uar_cell B));
  [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB 33%nat (as_uar_cell B) E33) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
  rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents.
unfold an_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 33%nat (as_uar_cell B) E33) by lia.
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 FFS Hstk0 Hob0 Hob1 Hob12 Huar Hsep. clear.
unfold ASAN_CEIL. intros.
rewrite !Z.add_0_r. repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
repeat split; first [ assumption | (apply or_comm; assumption)
| (repeat match goal with H : _ \/ _ |- _ => clear H end; lia) ].
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok an_atoms0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32, E33.
rewrite !unsigned_lit_small by (unfold SB in *; lia).
change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
repeat match goal with |- _ /\ _ => split end; unfold SB; lia.
Qed.
End c.
End b.
End a.
(* end of answer_e1 *)
