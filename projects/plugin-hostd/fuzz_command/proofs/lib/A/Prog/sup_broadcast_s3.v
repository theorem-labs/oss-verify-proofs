(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the last segment of plugin-hostd/fuzz_command's sup_broadcast walk, in the form
   of proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v (the step through a call): from the return of arg_line (0x8b048)
   the frame is restored and `j answer` (0x8b06c) runs answer at the entry stack pointer; answer's statement
   (a Section hypothesis) gives the post-condition.

   Pass-4/5 re-fit: TANSWER is taken at every FP state and used at the entry's fx (no
   earlier call changes the FP state); answer's rounding-mode-0 premise is the entry's (HFRM); answer is the last
   step, through PaFx.v's cl_callS_wideF, and PaFx.v's apost_baseF_intro closes sup_broadcast's apost_baseF.
   Statement pass 5 removed astack_pres, so no stack fact is built for answer's entry; the frame chain answer's
   afn_pre asks is sup_broadcast's own afn_pre chain (s0 at the tail jump is the entry s0), kept by achain_kept. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaLibG PaLibH PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_canonical_c rec_calls_free_c arg_line_c answer_c sup_broadcast_c PaNoChain PaFx sup_broadcast_s1 sup_broadcast_s2.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the symbolic state at 0x8b048: every register its own atom, the four saved words of the frame as the extra atoms
   32 (ra), 33 (s0), 34 (s1), 35 (s2); no window is written and no inline check is left *)
Definition sbt_stack : YP09.region := YP09.mkRegion (Some 2%nat) 0 32 0 0
[YP09.mkChunk 0 (CVal 8 (SOff 35 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0));
 YP09.mkChunk 16 (CVal 8 (SOff 33 0)); YP09.mkChunk 24 (CVal 8 (SOff 32 0))].
Definition ss_sbt : sstate := mkSS SB_RET_AL sr_atoms [sbt_stack] None (mkFacts [] [] []).
Definition sbt_Bx : sv := SLit SB_SB.
Definition sbt_SH : list shent := [].
Definition sbt_Bspan : Z * Z := (SB_SB, SB_SB + 2 ^ 44 - 1).
Definition sbt_extra (ra s0 s1 s2 : Z) : list word := map (Z_to_bv 64) [ra; s0; s1; s2].

(* the footprint of the statement (sup_broadcast_c.v:97-98) *)
Definition sb_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (A_G_REC + OFF_CALLS, A_G_REC + OFF_ANSWER + 8) ::
(A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the tail state's symbolic entry *)
Lemma sbt_entry : forall (W : world SEGS) regsA memA (ra s0 s1 s2 : Z),
0 <= ra < 2 ^ 64 -> 0 <= s0 < 2 ^ 64 -> 0 <= s1 < 2 ^ 64 -> 0 <= s2 < 2 ^ 64 -> spZ regsA + 32 <= 2 ^ 64 ->
aval_mem (rdW W memA) (spZ regsA + 24) 8 ra -> aval_mem (rdW W memA) (spZ regsA + 16) 8 s0 ->
aval_mem (rdW W memA) (spZ regsA + 8) 8 s1 -> aval_mem (rdW W memA) (spZ regsA) 8 s2 ->
st_ok_pi SEGS VAL (Eimg (Ereg regsA (sbt_extra ra s0 s1 s2))) ss_sbt
(restrict (w_H W) (mkst regsA (Z_to_bv 64 (BASE + SB_RET_AL)) memA (seg_rom SEGS))) /\
sh_ok SEGS sbt_Bx sbt_SH (Eimg (Ereg regsA (sbt_extra ra s0 s1 s2))) (mrestrict (w_H W) memA).
Proof.
intros W regsA memA ra s0 s1 s2 Hra Hs0 Hs1 Hs2 Hsp Vra Vs0 Vs1 Vs2.
set (E := Eimg (Ereg regsA (sbt_extra ra s0 s1 s2))).
assert (E2 : ew E 2 = getr regsA 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsA _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regsA) by (rewrite E2; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 ra) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsA _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 s0) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsA _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 s1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsA _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 s2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsA _ 3)).
assert (VM : forall H a v, aval_mem (aview SEGS H memA) a 8 v -> val_mem SEGS (mrestrict H memA) a 8 v).
{ intros H a v Hv kk Hk. specialize (Hv kk Hk). unfold aview in Hv.
  destruct (mbyte SEGS (mrestrict H memA) (a + Z.of_nat kk)) as [b|] eqn:Eb; cbn [option_map] in Hv; [|discriminate Hv].
  injection Hv as Hv. apply (f_equal (Z_to_bv 8)) in Hv. rewrite Z_to_bv_bv_unsigned in Hv. rewrite Hv. reflexivity. }
split.
- rewrite restrict_mkst_fx. unfold ss_sbt. apply pa_entry_st_ok_full.
  + subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold region_ok, sbt_stack.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
    pose proof (bv_unsigned_in_range 64 (getr regsA 2)) as Hr. unfold spZ in Hsp. change (bv_modulus 64) with (2 ^ 64) in Hr.
    split; [unfold spZ; lia|]. split; [unfold spZ; lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil;
    [ apply (chunk_ok_val SEGS E _ (spZ regsA) 0 8 (SOff 35 0) s2); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact (VM _ _ _ Vs2)]
    | apply (chunk_ok_val SEGS E _ (spZ regsA) 8 8 (SOff 34 0) s1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact (VM _ _ _ Vs1)]
    | apply (chunk_ok_val SEGS E _ (spZ regsA) 16 8 (SOff 33 0) s0); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact (VM _ _ _ Vs0)]
    | apply (chunk_ok_val SEGS E _ (spZ regsA) 24 8 (SOff 32 0) ra); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact (VM _ _ _ Vra)] ].
  + cbn. repeat split.
  + cbn. repeat split.
- unfold sh_ok, sbt_SH. apply Forall_nil.
Qed.

(* a reader at an address is the reader at its 64-bit residue *)
Lemma sb_aview_mod : forall (H : word -> bool) (m : word -> option byte) a, aview SEGS H m a = aview SEGS H m (a mod 2 ^ 64).
Proof.
intros H m a. unfold aview, mbyte, mrestrict.
replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma sb_bsum_nonneg : forall l : list (Z * Z), (forall b, In b l -> 0 <= snd b) -> 0 <= bsum l.
Proof.
induction l as [|b l IH]; intros H; [cbn; lia|]. rewrite bsum_cons.
pose proof (H b (or_introl eq_refl)). pose proof (IH (fun b' Hb' => H b' (or_intror Hb'))). lia.
Qed.

(* membership in the filter answer's footprint names (the filter these files see) *)
Lemma sb_in_filter : forall (l : list (Z * Z)) (old : Z) x, In x (filter (fun pn => fst pn =? old) l) -> In x l.
Proof.
induction l as [|y l IH]; intros old x H; [exact H|].
cbn in H. repeat match type of H with context [if ?c then _ else _] => destruct c end;
first [destruct H as [H | H]; [left; exact H | right; exact (IH old x H)] | right; exact (IH old x H)].
Qed.

Lemma sb_aregs : forall regs rT : bvmap 5 word,
getr rT (Z_to_bv 5 2) = getr regs (Z_to_bv 5 2) -> getr rT (Z_to_bv 5 3) = getr regs (Z_to_bv 5 3) ->
getr rT (Z_to_bv 5 4) = getr regs (Z_to_bv 5 4) -> getr rT (Z_to_bv 5 8) = getr regs (Z_to_bv 5 8) ->
getr rT (Z_to_bv 5 9) = getr regs (Z_to_bv 5 9) ->
(forall r, 18 <= r <= 27 -> getr rT (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
aregs_preserved regs rT.
Proof. intros regs rT H2 H3 H4 H8 H9 Hs r Hr. unfold acallee_saved in Hr. destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]]; auto. Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the per-binary record and the listing's atoms *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis SIGP : cmd_sig_prog.
(* fields of cmd_img_facts (CmdRecBase.v) and lemmas of CmdRecFacts.v, under their final names and forms until
   the kit has them (statement pass 3) *)
Hypothesis cif_prog_img : forall a, inFP cmd_PG a -> in_img SEGS a.
Hypothesis cmd_ro_in_img : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI).
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS CMD_RLO CMD_RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
(* answer's statement (sup_broadcast_c.v:65), at every FP state *)
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Let RUN := paj_run B LAWS.

(* the call target of answer *)
Lemma sb_sig_answer : SIGMA CS_answer = BASE + AF_answer.
Proof. rewrite (SIGP CS_answer); [reflexivity | cbn [cmd_prog_syms In]; repeat (first [left; reflexivity | right])]. Qed.

Lemma sb_arod_ext : forall (rd rd' : reader), (forall a, rd' a = rd a) ->
arodata_okP SEGS RLO RHI B rd -> arodata_okP SEGS RLO RHI B rd'.
Proof. intros rd rd' Hk HR a H1 H2 H3. rewrite Hk. exact (HR a H1 H2 H3). Qed.

Lemma sb_rep_ext : forall ly S (rd rd' : reader) R O, (forall a, rd' a = rd a) ->
rec_repA B ly S rd R O -> rec_repA B ly S rd' R O.
Proof.
intros ly S rd rd' R O Hk (Q & HA & HO). exists Q. split; [|exact HO].
apply (arep_at_agree _ _ rd rd' _ _ R Q HA); [intros pn _ H; exact H | intros j _; apply Hk | intros j _; apply Hk | intros pn _ j _; apply Hk].
Qed.

(* every byte of the statement's footprint lies below the allocator's ceiling *)
Lemma sb_FP_low : forall ly S (W : world SEGS) mem md O a, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> inFP (sb_FP O) a -> a < alloc_ceiling.
Proof.
intros ly S W mem md O a HAR HO Ha. pose proof asan_consts as (C1 & _).
unfold sb_FP in Ha. apply inFP_cons in Ha as [Ha | Ha]; [unfold A_G_REC, OFF_NCALLS in Ha; lia|].
apply inFP_cons in Ha as [Ha | Ha]; [unfold A_G_REC, OFF_CALLS, OFF_ANSWER in Ha; lia|].
apply inFP_cons in Ha as [Ha | Ha]; [unfold A_G_REC, OFF_STATE in Ha; lia|].
apply inFP_cons in Ha as [Ha | Ha]; [unfold A_REC_SPILL, SC_SIZE in Ha; lia|].
destruct (inFP_ablocks_fp_inv O a Ha) as (b & m & Hin & Hr).
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR (HO _ Hin)) as (_ & _ & Hc & _). lia.
Qed.

(* the post-condition of tsup_broadcast_spec (sup_broadcast_c.v:100-115) *)
Definition sb_post (ly : alayout) (S : astate) (R : rstate) (line : list byte) (O : list (Z * Z)) :
alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' =>
let t := snd (sup_broadcast_m R line) in
exists R' O' q,
 sup_broadcast_m R line = (R', t) /\
 let n := Z.of_nat (length t) + 1 in
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, n)) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 In (q, n) (ablocks B ly' S') /\ (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, n)) /\
 ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q t /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_BROADCAST line t /\
 mo_le MT S S' (XM_SUP_BROADCAST MT R line t).

(* answer's footprint for the old answer old and the recorder's blocks O (answer_c.v:115-116) *)
Definition sb_FPans (O : list (Z * Z)) (old : Z) : list (Z * Z) :=
(A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) ::
ablocks_fp (filter (fun pn => fst pn =? old) O).

(* 0x8b048 .. 0x8b06c and answer: from arg_line's return to the post-condition *)
Lemma sb_tail : forall ly S W regs mem md ch line R O lyA SA (WA : world SEGS) regsA memA mdA c F bl1 Omid p k,
afn_pre SEGS B SUP_BROADCAST_STK ly S W regs mem md ch ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
Z.of_nat (length (frames S)) <= 8 ->
rec_repA B ly S (rdW W mem) R O ->
st_nev S + EV_SUP_BROADCAST R <= EV_MAX ->
blocks_bytes S + LIVE_SUP_BROADCAST line (snd (sup_broadcast_m R line)) <= LIVE_MAX ->
mo_ok MT S (XM_SUP_BROADCAST MT R line (snd (sup_broadcast_m R line))) ->
ajournal SEGS B SUP_BROADCAST_STK (spZ regs) (sb_FP O) ly S W mem md [] lyA SA WA memA mdA (rec_spill_frees R + EV_ARG_LINE) ->
spZ regsA = spZ regs - 32 -> getr regsA 9 = w64 c -> 0 <= c < 2 ^ 64 ->
(forall r, acallee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 -> getr regsA (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
aval_mem (rdW WA memA) (spZ regs - 8) 8 (raZ regs) -> aval_mem (rdW WA memA) (spZ regs - 16) 8 (s0Z regs) ->
aval_mem (rdW WA memA) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
aval_mem (rdW WA memA) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
arodata_okP SEGS RLO RHI B (rdW WA memA) ->
rec_repA B lyA SA (rdW WA memA) (rec_record R REC_BROADCAST [canon line]) (Omid ++ [(p, k)]) ->
((exists kk, nth_error (r_calls (rec_record R REC_BROADCAST [canon line])) kk = Some (REC_BROADCAST, [canon line]) /\
  c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat kk) \/
 (c = A_REC_SPILL /\ (REC_BROADCAST, [canon line]) = r_spill (rec_record R REC_BROADCAST [canon line]))) ->
Permutation (ablocks B ly S) (bl1 ++ F) -> (forall pn, In pn F -> In pn O) ->
(forall pn, In pn Omid -> In pn O) -> (forall pn, In pn O -> In pn Omid \/ In pn F) ->
Permutation (ablocks B lyA SA) ((p, k) :: bl1) -> Forall (fun qk => iv_apart p k (fst qk) (snd qk)) bl1 ->
k = Z.of_nat (length line) + 1 ->
mo_le MT S SA (rec_spill_frees R * mo_free MT + XM_ARG_LINE MT line) ->
SRr SEGS WA (cfg_at SEGS (BASE + SB_RET_AL) regsA memA mdA)
(apost_baseF SEGS B SUP_BROADCAST_STK (sb_FP O) regs ly S W mem md (EV_SUP_BROADCAST R) (sb_post ly S R line O)).
Proof.
intros ly S W regs mem md ch line R O lyA SA WA regsA memA mdA c F bl1 Omid p k
HPRE HFRM Hfr8 HREC Hev Hlive HMOK HJ Hsp H9 Hc64 Hcs Vra Vs0 Vs1 Vs2 HROD HREC1 HCE HP0 HF0 HOm1 HOm2 HP1 HAp Hk HMLE.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WSTK : SUP_BROADCAST_STK = 16592) by reflexivity.
assert (WANS : ANSWER_STK = 16592) by reflexivity.
assert (HOb : forall pn, In pn O -> In pn (ablocks B ly S)) by (intros pn Hpn; exact (proj2 (sb_rep_pos _ _ _ _ pn HREC Hpn))).
destruct (sb_rep_old _ _ _ _ HREC1) as (old & Hold & Hold').
destruct (sbt_entry WA regsA memA (raZ regs) (s0Z regs) (bv_unsigned (getr regs 9)) (bv_unsigned (getr regs 18)))
as [HS SHOK];
[apply bv_unsigned_in_range | apply bv_unsigned_in_range | apply bv_unsigned_in_range | apply bv_unsigned_in_range | lia
| rewrite Hsp; replace (spZ regs - 32 + 24) with (spZ regs - 8) by lia; exact Vra
| rewrite Hsp; replace (spZ regs - 32 + 16) with (spZ regs - 16) by lia; exact Vs0
| rewrite Hsp; replace (spZ regs - 32 + 8) with (spZ regs - 24) by lia; exact Vs1
| rewrite Hsp; exact Vs2 |].
remember (sbt_extra (raZ regs) (s0Z regs) (bv_unsigned (getr regs 9)) (bv_unsigned (getr regs 18))) as X eqn:HX.
remember (Eimg (Ereg regsA X)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsA X) E) by (rewrite HE; split; [intros n Hn'; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsA r).
{ intros n r Hn. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E32 : ew E 32 = getr regs 1).
{ subst E X. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra regsA _ 0). apply Z_to_bv_bv_unsigned. }
assert (E33 : ew E 33 = getr regs 8).
{ subst E X. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra regsA _ 1). apply Z_to_bv_bv_unsigned. }
assert (E34 : ew E 34 = getr regs 9).
{ subst E X. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra regsA _ 2). apply Z_to_bv_bv_unsigned. }
assert (E35 : ew E 35 = getr regs 18).
{ subst E X. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra regsA _ 3). apply Z_to_bv_bv_unsigned. }
assert (E283 : ew E 283 = Z_to_bv 64 0x21ce0).
{ pose proof (HEI 283%nat ltac:(unfold A_TEXT, A_LIM; lia)) as H.
  change (VAL 283%nat) with (VAL (A_OBJ 42)) in H. rewrite (VOBJS 42%nat ltac:(vm_compute; lia)) in H.
  apply bv_eq. rewrite H. rewrite unsigned_lit_small by lia. vm_compute. reflexivity. }
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 32) by (rewrite (EE 2%nat 2%bv eq_refl); exact Hsp).
clear HE.
unfold cfg_at. change (w64 (BASE + SB_RET_AL)) with (Z_to_bv 64 (BASE + SB_RET_AL)).
paj_run_tok RUN HS HJ SHOK sbt_Bspan.
{ awr_ok_tac. }
pmkst HS.
lazymatch goal with |- context [with_vm_backing ?x ?y ?z] => set (mdv := with_vm_backing x y z) in *; clearbody mdv end.
(* the run writes nothing *)
assert (KEEP : forall a, rdW WA (ms_mem ms) a = rdW WA memA a).
{ intros a. rewrite (sb_aview_mod (w_H WA) (ms_mem ms) a), (sb_aview_mod (w_H WA) memA a).
  apply (kept_of_frame (segs:=SEGS) E _ (w_H WA) memA (ms_mem ms) (fun _ => False) HFr).
  - intros b wlo whi a' Hin Hr. vm_compute in Hin.
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; lia|]). destruct Hin.
  - apply Z.mod_pos_bound. lia.
  - intros []. }
clear HF HFr HG.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9.
prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (12%bv : bv 5) T12. prreg HS (18%bv : bv 5) T18.
rewrite E32 in T1. rewrite E33 in T8. rewrite E34 in T9. rewrite E35 in T18. rewrite E283 in T11.
rewrite (EE 9%nat 9%bv eq_refl), H9 in T10.
pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hr2. change (bv_modulus 64) with (2 ^ 64) in Hr2.
assert (T2' : getr (ms_regs ms) 2 = getr regs 2).
{ rewrite T2, Usp. replace (spZ regs - 32 + 32) with (spZ regs) by lia. apply Z_to_bv_bv_unsigned. }
assert (Hsp2 : spZ (ms_regs ms) = spZ regs + 0) by (unfold spZ; rewrite T2'; lia).
pose proof (regs_kept_of_st_ok SEGS E _ _ regsA X (map (Z_to_bv 5) [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]) HS HAE
  ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
assert (KR' : forall r, In r [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. rewrite (KR (Z_to_bv 5 r) (in_map _ _ _ Hr)). apply Hcs.
  - unfold acallee_saved. cbn [In] in Hr. lia.
  - cbn [In] in Hr; lia. - cbn [In] in Hr; lia. - cbn [In] in Hr; lia. - cbn [In] in Hr; lia. }
assert (T3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (etransitivity; [exact (KR' 3 ltac:(cbn; tauto)) | exact Hgp]).
assert (T4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (etransitivity; [exact (KR' 4 ltac:(cbn; tauto)) | exact Htp]).
assert (HPT : aregs_preserved regs (ms_regs ms)).
{ apply sb_aregs; [exact T2' | apply KR'; cbn; tauto | apply KR'; cbn; tauto | exact T8 | exact T9 |].
  intros r Hr. assert (Hr' : r = 18 \/ In r [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]) by (cbn [In]; lia).
  destruct Hr' as [-> | Hr']; [exact T18 | exact (KR' r Hr')]. }
pose proof HJ as (HART & HlyT & _ & _ & _ & HfrsT & HnevT & _ & F1T & _).
pose proof HlyT as (_ & _ & _ & _ & _ & _ & _ & _ & EtopT & _).
assert (HRODT : arodata_okP SEGS RLO RHI B (rdW WA (ms_mem ms))) by exact (sb_arod_ext _ _ KEEP HROD).
assert (HRECT : rec_repA B lyA SA (rdW WA (ms_mem ms)) (rec_record R REC_BROADCAST [canon line]) (Omid ++ [(p, k)]))
  by exact (sb_rep_ext _ _ _ _ _ _ KEEP HREC1).
assert (HbA : forall pn, In pn (Omid ++ [(p, k)]) -> In pn (ablocks B lyA SA))
  by (intros pn Hpn; exact (proj2 (sb_rep_pos (ablocks B lyA SA) (rdW WA memA) _ _ pn HREC1 Hpn))).
assert (Hk0 : 0 < k) by lia.
assert (HpF : In (p, k) (ablocks B ly S) -> In (p, k) O).
{ intros H0. apply (Permutation_in _ HP0) in H0. apply in_app_or in H0 as [H0 | H0]; [|exact (HF0 _ H0)].
  exfalso. pose proof (proj1 (Forall_forall _ _) HAp _ H0) as Hd. unfold iv_apart in Hd. cbn [fst snd] in Hd. lia. }
eapply SRr_mono.
{ eapply (cl_callS_wideF B LAWS WA (ms_regs ms) (ms_mem ms) (Z_to_bv 64 (SIGMA CS_answer))
    SUP_BROADCAST_STK (spZ regs) (sb_FP O) ly S W mem md [] lyA SA mdv (rec_spill_frees R + EV_ARG_LINE)
    ANSWER_STK (sb_FPans (Omid ++ [(p, k)]) old) EV_ANSWER 0 (getr regs 1) ch _ HJ Hsp2).
  - reflexivity.
  - lia.
  - rewrite WANS. lia.
  - rewrite WANS, WSTK. lia.
  - exact T3.
  - exact T4.
  - exact T1.
  - exact Hra.
  - exact Hra4.
  - (* the frame chain at the tail jump: the entry's, above sp *)
    replace (spZ regs + 0) with (spZ regs) by lia.
    assert (Hs0 : s0Z (ms_regs ms) = s0Z regs) by (unfold s0Z; rewrite T8; reflexivity). rewrite Hs0.
    apply (achain_ly_top ly lyA _ _ _ _ EtopT).
    apply (achain_kept ly (rdW W mem) _ (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | lia |].
    intros a Ha. apply F1T; [lia | lia |].
    intros Hf. pose proof (sb_FP_low ly S W mem md O a HAR HOb Hf). lia.
  - (* answer's statement *)
    intros HPRE2. rewrite sb_sig_answer.
    assert (HROT : cmd_ro_ok (rdW WA (ms_mem ms))) by exact (cmd_ro_ok_of_aro lyA SA WA (ms_mem ms) mdv HART HRODT).
    assert (HRO7 : forall i, 0 <= i < 7 -> in_roP SEGS RLO RHI (0x21ce0 + i)).
    { pose proof cmd_ro_in_img as HROIN. clear - HROIN. unfold cmd_ro_in in HROIN.
      repeat match type of HROIN with
      | (forall i : Z, 0 <= i < 7 -> in_roP _ _ _ (0x21ce0 + i)) /\ _ => exact (proj1 HROIN)
      | _ /\ _ => apply proj2 in HROIN
      end. }
    assert (Hold64 : 0 <= old < 2 ^ 64).
    { destruct Hold' as [-> | (ko & Hko)]; [lia|].
      destruct (al_blocks _ _ LAWS lyA SA WA (ms_mem ms) mdv old ko HART (HbA _ Hko)) as (_ & H4k & Hck & _ & _ & _ & Hmk).
      pose proof (req_size_pos ko ltac:(lia)) as [Hrq _]. lia. }
    eapply SRr_mono.
    { apply (TANSWER fx lyA SA WA (ms_regs ms) (ms_mem ms) mdv ch c 0x21ce0 old (REC_BROADCAST, [canon line])
        REC_MOD_HOST_SHAPE true (rec_record R REC_BROADCAST [canon line]) (Omid ++ [(p, k)]) HPRE2).
      - exact HFRM.
      - rewrite HfrsT. exact Hfr8.
      - exact HRODT.
      - exact HROT.
      - exact T10.
      - exact Hc64.
      - exact T11.
      - lia.
      - rewrite T12, unsigned_lit_small by lia. reflexivity.
      - exact HRECT.
      - intros kk Hkk. rewrite KEEP. exact (Hold kk Hkk).
      - exact Hold64.
      - intros _. split.
        + unfold astr_argA. split; [lia|]. split.
          * split.
            -- assert (EL : REC_MOD_HOST_SHAPE ++ [Z_to_bv 8 0] = RO_lit_21ce0) by (vm_compute; reflexivity).
               rewrite EL. destruct HROT as [HROB _]. unfold cmd_ro_bytes in HROB.
               repeat match type of HROB with
               | abytes_atR _ 0x21ce0 _ /\ _ => exact (proj1 HROB)
               | _ /\ _ => apply proj2 in HROB
               end.
            -- unfold REC_MOD_HOST_SHAPE. cbn. intros H. repeat (destruct H as [H|H]; [vm_compute in H; discriminate H|]). exact H.
          * change (Z.of_nat (length REC_MOD_HOST_SHAPE) + 1) with 7. split; [unfold LMAX; lia|].
            right. split; [intros i Hi; split; [exact (HRO7 i Hi) | exact (sb_shape_unowned B HB i Hi)]|].
            split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
            change (0x21ce0 + Z.of_nat (length REC_MOD_HOST_SHAPE)) with 0x21ce6.
            assert (Hend : existsb (Z.eqb 0x21ce6) cmd_ro_ends = true) by (vm_compute; reflexivity).
            apply existsb_exists in Hend as (x & Hx & Hxe). apply Z.eqb_eq in Hxe. rewrite Hxe. exact Hx.
        + unfold fits. assert (Hf : (Z.of_nat (length (inst REC_MOD_HOST_SHAPE)) <=? PHD_LINE_MAX - 1) = true)
            by (vm_compute; reflexivity). apply Z.leb_le in Hf. exact Hf.
      - intros _ _. exact HCE.
      - unfold EV_SUP_BROADCAST in Hev. lia.
      - rewrite (blocks_bytes_bsum B lyA SA), (bsum_perm _ _ HP1), bsum_cons. cbn [snd].
        rewrite (blocks_bytes_bsum B ly S), (bsum_perm _ _ HP0), bsum_app in Hlive.
        assert (HFn : 0 <= bsum F).
        { apply sb_bsum_nonneg. intros [b m] Hb. pose proof (HOb _ (HF0 _ Hb)) as Hb0.
          destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hb0) as (_ & _ & _ & _ & _ & _ & Hm). cbn [snd]. lia. }
        unfold LIVE_SUP_BROADCAST, LIVE_ARG_LINE, LIVE_REC_CANONICAL, sup_broadcast_m, rec_stub in Hlive. lia.
      - unfold XM_SUP_BROADCAST in HMOK.
        exact (mo_ok_step MT MTL S SA (rec_spill_frees R * mo_free MT + XM_ARG_LINE MT line) _ HMOK HMLE). }
    cbv beta. unfold apost_baseF. intros W2 c2 _ (fx1 & ly2 & S2 & regs2 & mem2 & md2 & -> & Hf1 & Hf2 & HJ2 & HP2 & HK2).
    exists fx1, ly2, S2, regs2, mem2, md2. split; [rewrite T1; reflexivity|]. split; [exact Hf1|]. split; [exact Hf2|].
    split; [exact HJ2|]. split; [exact HP2 | exact HK2].
  - (* answer's footprint: g_rec's answer and state words, and the old answer's block *)
    intros a Ha. unfold awr_byte, awr_prog_or_caller. unfold sb_FPans in Ha.
    assert (HPG : forall a, A_G_REC <= a < A_G_REC + 960 -> inFP cmd_PG a)
      by (intros a0 Ha0; exists (A_G_REC, A_G_REC + 960); split; [left; reflexivity | cbn [fst snd]; lia]).
    apply inFP_cons in Ha as [Ha | Ha]; [|apply inFP_cons in Ha as [Ha | Ha]].
    + do 4 right. left. unfold A_G_REC, OFF_ANSWER in Ha.
      split; [unfold sb_FP; apply inFP_cons; right; apply inFP_cons; left; unfold A_G_REC, OFF_CALLS, OFF_ANSWER; lia|].
      split; [apply (HPROG B HB); apply HPG; unfold A_G_REC; lia | apply cif_prog_img; apply HPG; unfold A_G_REC; lia].
    + do 4 right. left. unfold A_G_REC, OFF_STATE in Ha.
      split; [unfold sb_FP; apply inFP_cons; right; apply inFP_cons; right; apply inFP_cons; left; unfold A_G_REC, OFF_STATE; lia|].
      split; [apply (HPROG B HB); apply HPG; unfold A_G_REC; lia | apply cif_prog_img; apply HPG; unfold A_G_REC; lia].
    + destruct (inFP_ablocks_fp_inv _ a Ha) as (b & m & Hin & Hr). apply sb_in_filter in Hin.
      pose proof (HbA _ Hin) as HbmA.
      assert (HinFP : In (b, m) O -> inFP (sb_FP O) a).
      { intros HO. unfold sb_FP. do 4 (apply inFP_cons; right). replace a with (b + (a - b)) by lia.
        apply (inFP_ablocks_fp O b m (a - b)); [exact HO | lia]. }
      apply in_app_or in Hin as [HinM | [Hpk | []]].
      * right. left. split; [exact (HinFP (HOm1 _ HinM)) | exists b, m; split; [exact HbmA | exact Hr]].
      * injection Hpk as <- <-.
        destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, k) (ablocks B ly S)) as [H0 | H0].
        -- right. left. split; [exact (HinFP (HpF H0)) | exists p, k; split; [exact HbmA | exact Hr]].
        -- right. right. left. exists p, k. split; [exact HbmA|]. split; [exact H0 | exact Hr].
  - (* no footprint byte of answer lies in sup_broadcast's stack window *)
    intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso. unfold sb_FPans in Ha.
    apply inFP_cons in Ha as [Ha | Ha]; [unfold A_G_REC, OFF_ANSWER in Ha; lia|].
    apply inFP_cons in Ha as [Ha | Ha]; [unfold A_G_REC, OFF_STATE in Ha; lia|].
    destruct (inFP_ablocks_fp_inv _ a Ha) as (b & m & Hin & Hr). apply sb_in_filter in Hin.
    destruct (al_blocks _ _ LAWS lyA SA WA (ms_mem ms) mdv b m HART (HbA _ Hin)) as (_ & _ & Hc & _). lia. }
(* the post-condition *)
cbv beta. intros W2 c2 _ (fx1 & ly2 & S2 & regs2 & mem2 & md2 & Hfx & -> & HJ3 & _ & HP3 & HK3).
destruct HK3 as (p1 & p2 & O' & HK3). cbv zeta in HK3.
destruct HK3 as (Hq10 & Hq4096 & Hp12 & Hfr3 & Hbl3 & Hrep3 & HO3 & Hstr3 & Hbb3 & Hmle3).
(* answer returned at fx1 with fxrel fx fx1: that is sup_broadcast's apost_baseF *)
apply (apost_baseF_intro (fx := fx) SEGS fx1 _ _ _ _ _ _ _ _ _ _ _ _ ly2 S2);
  [exact Hfx | eapply (ajournal_mono_k SEGS B); [exact HJ3 | unfold EV_SUP_BROADCAST; lia]
  | exact (aregs_preserved_trans _ _ _ HPT HP3) |].
unfold sb_post. exists (fst (sup_broadcast_m R line)), O', p2.
split; [apply surjective_pairing|].
cbv zeta.
destruct (sb_post_blocks (ablocks B ly S) bl1 (ablocks B lyA SA) (ablocks B ly2 S2) O Omid F O' p k p1 p2
  (Z.of_nat (length (snd (sup_broadcast_m R line))) + 1) old) as (P1 & P2 & P3 & P4 & P5 & P7).
{ exact (sb_blocks_nodup B LAWS ly S W mem md HAR). }
{ exact (sb_blocks_nodup B LAWS lyA SA WA (ms_mem ms) mdv HART). }
{ exact (sb_blocks_nodup B LAWS ly2 S2 W2 mem2 md2 (proj1 HJ3)). }
{ exact HOb. } { exact HP0. } { exact HF0. } { exact HOm1. } { exact HOm2. }
{ intros pn Hpn. exact (HbA pn (in_or_app _ _ _ (or_introl Hpn))). }
{ exact HP1. } { exact HAp. } { exact Hk0. }
{ exact Hbl3. } { exact Hfr3. } { exact Hp12. } { exact HO3. } { exact Hold'. }
{ intros [b m] Hin. destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & H4096 & _). cbn [fst]. lia. }
{ intros pn Hpn. exact (proj2 (sb_rep_pos (ablocks B ly2 S2) (rdW W2 mem2) _ _ pn Hrep3 Hpn)). }
split; [exact Hq10|]. split; [exact Hq4096|]. split; [exact Hrep3|].
split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
split; [exact P4|]. split; [exact P5|].
split; [exact P7|]. split; [exact Hstr3|].
split.
{ (* the live bytes: arg_line's block (p, k) beside the survivors bl1, then answer's two copies *)
  rewrite (blocks_bytes_bsum B lyA SA), (bsum_perm _ _ HP1), bsum_cons in Hbb3. cbn [snd] in Hbb3.
  rewrite (blocks_bytes_bsum B ly S), (bsum_perm _ _ HP0), bsum_app.
  assert (HFn : 0 <= bsum F).
  { apply sb_bsum_nonneg. intros [b m] Hb. pose proof (HOb _ (HF0 _ Hb)) as Hb0.
    destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hb0) as (_ & _ & _ & _ & _ & _ & Hm). cbn [snd]. lia. }
  unfold LIVE_SUP_BROADCAST, LIVE_ARG_LINE, LIVE_REC_CANONICAL, sup_broadcast_m, rec_stub in Hbb3 |- *. lia. }
unfold XM_SUP_BROADCAST. exact (mle_station MT S SA S2 _ _ MTL HMLE Hmle3).
Qed.

End e.
End f.
End d.
