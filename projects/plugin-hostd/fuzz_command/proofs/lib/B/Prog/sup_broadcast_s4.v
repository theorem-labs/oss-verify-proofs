(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the head of the sup_broadcast walk on fuzz_command.asan-ubsan and its call of
   record: the run 0x8b4f0 .. `jal record` (0x8b508) over the verified symbolic executor (the own 32-byte frame:
   ra, s0, s1 saved at sp + 24, 16, 8; `mv s0,a0`; `li a0,5`), the state it reaches (sbb_at_rec), the call of
   record through the kit's call rule for a callee whose footprint holds program statics (PaCallPg.v cl_callS_pg,
   with record_c.v's contract at the walk's FP state), and the state at record's return (0x8b50c, sbb_ret_rec).
   The run is the shape of a Theorem Labs lane's A walk (lib/A/Prog/sup_broadcast_s6.v, _s8.v at a5a5ff08765) with the head's
   record() body moved into the callee. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaLibG.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts PaNoChain PaCallPg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import RecBLemmas RecBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
xmalloc_c rec_canonical_c hand_back_c record_c arg_line_c answer_c sup_broadcast_c sup_broadcast_s1 sup_broadcast_s2 sup_broadcast_s3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the symbolic state at the entry: the own frame (written) and nothing else; no shadow byte is read *)
Definition sbb_e_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition ss_sbb_e : sstate := mkSS AF_sup_broadcast sr_atoms [stack_region 32] None sbb_e_facts.
Definition SBB_SB : Z := 0x7fff8000.
Definition sbb_Bx : sv := SLit SBB_SB.
Definition sbb_SH : list shent := [].
Definition sbb_Bspan : Z * Z := (SBB_SB, SBB_SB + 2 ^ 44 - 1).
(* the frame after the prologue (sd ra,24(sp); sd s0,16(sp); sd s1,8(sp) after sp -= 32) *)
Definition sbb_e_stack : YP09.region := YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0
[YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a chunk of a region of the symbolic state shows its value in memory (A: sup_broadcast_s5.v sb_chunk_val) *)
Lemma sbb_chunk_val : forall (H : word -> bool) E ss ms i r j off (n : N) e v,
st_ok SEGS E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
nth_error (YP09.r_chunks r) j = Some (YP09.mkChunk off (CVal n e)) ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
val_mem SEGS (mrestrict H (ms_mem ms)) (base_val E (YP09.r_base r) + off) (N.to_nat n) v.
Proof.
intros H E ss ms i r j off n e v HS Hi Hj He Hv Hn.
pose proof (st_ok_mem_ok SEGS E ss _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)) as (_ & _ & _ & Hcs).
apply (val_of_chunk_ok SEGS E _ _ off n e v); [|exact He | exact Hv | exact Hn].
exact (proj1 (Forall_forall _ _) Hcs _ (nth_error_In _ _ Hj)).
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Let RUN := paj_run B LAWS.

(* the stack this walk needs (gen/funcs.tsv's measurements, by computation): its own 32-byte frame above record's
   need (the deeper of record and arg_line), equal to answer's, which the tail jump runs at the entry sp *)
Lemma sbb_stk : SUP_BROADCAST_STK = 16592 /\ RECORD_STK = 16560 /\ ARG_LINE_STK = 16480 /\ ANSWER_STK = 16592.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* a live block: its bounds and size *)
Lemma sbb_blk : forall ly S (W : world SEGS) mem md p n, AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
4096 <= p /\ p + req_size n <= alloc_ceiling /\ 0 <= n /\ 1 <= req_size n /\ n <= req_size n.
Proof.
intros ly S W mem md p n HAR Hin.
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & H1 & H2 & _ & _ & _ & H3).
pose proof (req_size_pos n ltac:(lia)). lia.
Qed.

(* the call target of record *)
Lemma sbb_sig_record : SIGMA CS_record = BASE + AF_record.
Proof. rewrite (SIGP CS_record); [reflexivity | cbn [cmd_prog_syms In]; repeat (first [left; reflexivity | right])]. Qed.

(* the slot record() takes is a slot of g_rec's table or record.spill: rec_repA bounds the table by 16 calls *)
Lemma sbb_rec_slot_ok : forall ly S (rd : reader) R O, rec_repA B ly S rd R O -> sb_slot (rec_slot R).
Proof.
intros ly S rd R O (Q & HA & _). pose proof HA as (_ & _ & _ & (HL16 & _) & _).
unfold rec_slot, sb_slot. destruct (Nat.ltb (length (r_calls R)) 16) eqn:E; [|right; reflexivity].
apply Nat.ltb_lt in E. left. exists (Z.of_nat (length (r_calls R))). unfold REC_CALLS_MAX. split; [lia | reflexivity].
Qed.

(* a byte of a program static is a byte the walk may write: awr_byte's program-static disjunct *)
Lemma sbb_pg_prog : forall a, inFP cmd_PG a -> Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a.
Proof. intros a Ha. split; [exact (HPROG B HB a Ha) | exact (cif_prog_img _ _ IMG a Ha)]. Qed.

(* a read-only byte is an image byte below kLowMemEnd *)
Lemma sbb_ro_low : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ 0 <= a < kLowMemEnd.
Proof.
intros a Ha. assert (Hi : in_img SEGS a)
  by (destruct Ha as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (cif_relro_img _ _ IMG a Hr)]).
split; [exact Hi | exact (pa_segs_low a Hi)].
Qed.

(* the entry's symbolic state *)
Lemma sbb_e_entry : forall ly S (W : world SEGS) regs mem md ch,
afn_pre SEGS B SUP_BROADCAST_STK ly S W regs mem md ch ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) ss_sbb_e
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sup_broadcast)) mem (seg_rom SEGS))) /\
sh_ok SEGS sbb_Bx sbb_SH (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct sbb_stk as (WSTK & _).
set (E := Eimg (Ereg regs [])).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
split.
- rewrite restrict_mkst_fx. unfold ss_sbb_e. apply pa_entry_st_ok_full.
  + subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold region_ok, stack_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
  + split; [|split; [exact I | exact I]].
    cbn [sbb_e_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp. change (2 ^ 4) with 16.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
- unfold sh_ok, sbb_SH. apply Forall_nil.
Qed.

(* the run 0x8b4f0 .. `jal record`: the facts at record's entry go to the continuation *)
Lemma sbb_reach_rec : forall ly S W regs mem md ch O (Qk : world SEGS -> config -> Prop),
afn_pre SEGS B SUP_BROADCAST_STK ly S W regs mem md ch ->
(forall regsX memX mdX,
 ajournal SEGS B SUP_BROADCAST_STK (spZ regs) (sb_FP O) ly S W mem md [] ly S W memX mdX 0 ->
 spZ regsX = spZ regs - 32 ->
 getr regsX 1 = Z_to_bv 64 (BASE + SBB_RET_REC) ->
 getr regsX 8 = getr regs 10 ->
 getr regsX 10 = w64 REC_BROADCAST ->
 (forall r, acallee_saved r -> r <> 2 -> r <> 8 -> getr regsX (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
 sbb_frame regs (rdW W memX) ->
 (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) -> rdW W memX a = rdW W mem a) ->
 SRr SEGS W (mkCfg (mkst regsX (Z_to_bv 64 (SIGMA CS_record)) memX (seg_rom SEGS)) mdX) Qk) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_broadcast) regs mem md) Qk.
Proof.
intros ly S W regs mem md ch O Qk HPRE HK.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct (sbb_e_entry ly S W regs mem md ch HPRE) as [HS SHOK].
pose proof (ajournal_init SEGS B SUP_BROADCAST_STK (sb_FP O) ly S W regs mem md ch HPRE) as HJ.
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E) by (rewrite HE; split; [intros n Hn'; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r).
{ intros k r Hk. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. }
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
clear HE.
unfold cfg_at. change (w64 (BASE + AF_sup_broadcast)) with (Z_to_bv 64 (BASE + AF_sup_broadcast)).
paj_run_tok RUN HS HJ SHOK sbb_Bspan.
{ awr_ok_tac; exact Usp. }
pmkst HS.
lazymatch goal with |- context [with_vm_backing ?x ?y ?z] => set (mdv := with_vm_backing x y z) in *; clearbody mdv end.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10.
pose proof HS as HSo. unfold st_ok_pi in HSo.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) -> rdW W (ms_mem ms) a = rdW W mem a) by
 (intros a Ha H1; apply (kept_of_frame (segs:=SEGS) E _ (w_H W) mem (ms_mem ms) (fun a => spZ regs - 32 <= a < spZ regs) HFr);
  [ intros b wlo whi a' Hin Hr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite ?Usp in Hr; cbv beta; lia|]);
    destruct Hin
  | exact Ha | exact H1 ]).
assert (Vs1 : aval_mem (rdW W (ms_mem ms)) (spZ regs - 24) 8 (bv_unsigned (getr regs 9))) by
 (apply aval_mem_view;
  replace (spZ regs - 24) with (base_val E (YP09.r_base sbb_e_stack) + -24) by (cbn [YP09.r_base base_val sbb_e_stack]; rewrite Usp; lia);
  apply (sbb_chunk_val (w_H W) E _ ms 0%nat sbb_e_stack 0%nat (-24) 8 (SOff 9 0) (bv_unsigned (getr regs 9)) HSo);
  [ vm_compute; reflexivity | vm_compute; reflexivity
  | cbn [sv_denot]; rewrite Z.add_0_r, (EE 9%nat 9%bv eq_refl); first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity]
  | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact (bv_unsigned_in_range 64 (getr regs 9))
  | cbn; lia ]).
assert (Vs0 : aval_mem (rdW W (ms_mem ms)) (spZ regs - 16) 8 (s0Z regs)) by
 (apply aval_mem_view;
  replace (spZ regs - 16) with (base_val E (YP09.r_base sbb_e_stack) + -16) by (cbn [YP09.r_base base_val sbb_e_stack]; rewrite Usp; lia);
  apply (sbb_chunk_val (w_H W) E _ ms 0%nat sbb_e_stack 1%nat (-16) 8 (SOff 8 0) (s0Z regs) HSo);
  [ vm_compute; reflexivity | vm_compute; reflexivity
  | cbn [sv_denot]; rewrite Z.add_0_r, (EE 8%nat 8%bv eq_refl); first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity]
  | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact (bv_unsigned_in_range 64 (getr regs 8))
  | cbn; lia ]).
assert (Vra : aval_mem (rdW W (ms_mem ms)) (spZ regs - 8) 8 (raZ regs)) by
 (apply aval_mem_view;
  replace (spZ regs - 8) with (base_val E (YP09.r_base sbb_e_stack) + -8) by (cbn [YP09.r_base base_val sbb_e_stack]; rewrite Usp; lia);
  apply (sbb_chunk_val (w_H W) E _ ms 0%nat sbb_e_stack 2%nat (-8) 8 (SOff 1 0) (raZ regs) HSo);
  [ vm_compute; reflexivity | vm_compute; reflexivity
  | cbn [sv_denot]; rewrite Z.add_0_r, (EE 1%nat 1%bv eq_refl); first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity]
  | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact (bv_unsigned_in_range 64 (getr regs 1))
  | cbn; lia ]).
pose proof (regs_kept_of_st_ok SEGS E _ _ regs [] (map (Z_to_bv 5) [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]) HS HAE
  ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
clear HF HFr HG.
apply HK.
- exact HJ.
- unfold spZ at 1. rewrite P2, Usp. rewrite unsigned_lit_small by lia. lia.
- rewrite P1. unfold SBB_RET_REC, AF_sup_broadcast. reflexivity.
- rewrite P8. exact (EE 10%nat 10%bv eq_refl).
- rewrite P10. reflexivity.
- intros r Hr H2 H8. apply KR. apply in_map. unfold acallee_saved in Hr. cbn [In]. lia.
- split; [exact Vra | split; [exact Vs0 | exact Vs1]].
- exact KEEP.
Qed.

(* record's entry state, with the recorder and the read-only view carried over the frame writes *)
Lemma sbb_at_rec_of : forall ly S W regs mem md ch pl line R O regsX memX mdX,
sbb_ent B MT ly S W regs mem md ch pl line R O ->
ajournal SEGS B SUP_BROADCAST_STK (spZ regs) (sb_FP O) ly S W mem md [] ly S W memX mdX 0 ->
spZ regsX = spZ regs - 32 ->
getr regsX 1 = Z_to_bv 64 (BASE + SBB_RET_REC) ->
getr regsX 8 = getr regs 10 ->
getr regsX 10 = w64 REC_BROADCAST ->
(forall r, acallee_saved r -> r <> 2 -> r <> 8 -> getr regsX (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
sbb_frame regs (rdW W memX) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) -> rdW W memX a = rdW W mem a) ->
sbb_at_rec B ly S W regs mem md pl R O regsX memX mdX.
Proof.
intros ly S W regs mem md ch pl line R O regsX memX mdX HENT HJ Hsp R1 R8 R10 RCS VF KEEP.
destruct HENT as (HPRE & HFRM & Hfr8 & HROD & H10 & Hpl & HBLK & HAP & HSTR & HLEN & HREC & Hev & Hlive & HMOK).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct sbb_stk as (WSTK & _).
assert (KL : forall a, 0 <= a < alloc_ceiling -> rdW W memX a = rdW W mem a) by (intros a Ha; apply KEEP; lia).
split; [exact HJ|]. split; [exact Hsp|]. split; [exact R1|]. split; [rewrite R8; exact H10|].
split; [exact R10|]. split; [exact RCS|]. split; [exact VF|]. split; [exact KEEP|]. split.
- intros a H1 H2 H3. destruct (sbb_ro_low a H1) as (_ & Ha). rewrite KL by lia. exact (HROD a H1 H2 H3).
- apply (rec_repA_kept B ly S (rdW W mem) ly S (rdW W memX) R O HREC); [intros pn Hpn; exact (proj2 (sbb_rep_pos B _ _ _ _ _ pn HREC Hpn))|].
  intros a Ha. apply KL. destruct Ha as [Ha | [Ha | Ha]].
  + unfold A_G_REC, REC_SIZE in Ha. lia.
  + unfold A_REC_SPILL, SC_SIZE in Ha. lia.
  + destruct (inFP_ablocks_fp_inv O a Ha) as (b & m & Hin & Hr).
    pose proof (sbb_blk ly S W mem md b m HAR (proj2 (sbb_rep_pos B _ _ _ _ _ _ HREC Hin))). lia.
Qed.

(* every byte of record's footprint is a block byte or a program static of the image, in the walk's footprint *)
Lemma sbb_rec_fp_ok : forall ly S (W : world SEGS) mem md R O, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> sb_slot (rec_slot R) ->
forall a, inFP (sbb_rec_FP R O) a ->
(inFP (sb_FP O) a /\ ((exists b n, In (b, n) (ablocks B ly S) /\ b <= a < b + req_size n) \/
 (Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a))) \/ in_tmp_block (ablocks B ly S) (ablocks B ly S) a.
Proof.
intros ly S W mem md R O HAR HOb Hsl a Ha. left. unfold sbb_rec_FP in Ha.
apply inFP_cons in Ha as [Ha | Ha].
- split; [unfold sb_FP; apply inFP_cons; left; exact Ha|]. right. apply sbb_pg_prog.
  exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; unfold OFF_NCALLS in Ha; lia].
- apply inFP_cons in Ha as [Ha | Ha].
  + split; [apply (sb_slot_fp (rec_slot R)); [exact Hsl | lia]|]. right. apply sbb_pg_prog.
    apply (sb_slot_pg (rec_slot R)); [exact Hsl | unfold CALL_SIZE; lia].
  + destruct (Nat.ltb (length (r_calls R)) 16); [exfalso; exact (inFP_nil a Ha)|].
    destruct (inFP_ablocks_fp_inv O a Ha) as (b & m & Hin & Hr). split.
    * unfold sb_FP. do 4 (apply inFP_cons; right). exact Ha.
    * left. exists b, m. split; [exact (HOb _ Hin) | exact Hr].
Qed.

(* the call of record: cl_callS_pg with record's contract at the walk's FP state *)
Lemma sbb_call_record : forall ly S W regs mem md ch pl line R O regsX memX mdX,
sbb_ent B MT ly S W regs mem md ch pl line R O ->
sbb_at_rec B ly S W regs mem md pl R O regsX memX mdX ->
SRr SEGS W (mkCfg (mkst regsX (Z_to_bv 64 (SIGMA CS_record)) memX (seg_rom SEGS)) mdX)
(sbb_post_rec B MT ly S W regs mem md R O regsX memX mdX).
Proof.
intros ly S W regs mem md ch pl line R O regsX memX mdX HENT HAT.
destruct HENT as (HPRE & HFRM & Hfr8 & HROD & H10 & Hpl & HBLK & HAP & HSTR & HLEN & HREC & Hev & Hlive & HMOK).
destruct HAT as (HJ & Hsp & R1 & R8 & R10 & RCS & VF & KEEP & HROD1 & HREC1).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct sbb_stk as (WSTK & WREC & WAL & WANS).
assert (HOb : forall pn, In pn O -> In pn (ablocks B ly S)) by (intros pn Hpn; exact (proj2 (sbb_rep_pos B _ _ _ _ _ pn HREC Hpn))).
destruct HBLK as (pb & kb & Hinb & Hpb1 & Hpb2).
destruct (sbb_blk ly S W mem md pb kb HAR Hinb) as (Hb4 & Hbc & Hkb0 & _ & Hkbr).
pose proof (sbb_rec_slot_ok ly S _ R O HREC) as Hsl.
assert (HEVR : st_nev S + EV_RECORD R <= EV_MAX).
{ unfold EV_SUP_BROADCAST, EV_ARG_LINE, EV_ANSWER, EV_REC_CANONICAL, EV_HAND_BACK, EV_XMALLOC in Hev. lia. }
assert (HMOKR : mo_ok MT S (XM_RECORD MT R)).
{ apply (mo_ok_le MT MTL S _ _ HMOK). unfold XM_SUP_BROADCAST.
  assert (0 <= XM_ARG_LINE MT line) by (unfold XM_ARG_LINE, XM_REC_CANONICAL, XM_XMALLOC; apply (mo_malloc_nonneg MT MTL); unfold LIVE_XMALLOC; lia).
  assert (0 <= XM_ANSWER MT (snd (sup_broadcast_m R line))).
  { unfold XM_ANSWER, XM_HAND_BACK, XM_XMALLOC. pose proof (mo_free_nonneg MT MTL).
    pose proof (mo_malloc_nonneg MT MTL (LIVE_XMALLOC (Z.of_nat (length (snd (sup_broadcast_m R line))) + 1))
      ltac:(unfold LIVE_XMALLOC; lia)). lia. }
  lia. }
unfold sbb_post_rec.
eapply SRr_mono.
{ eapply (cl_callS_pg B LAWS W regsX memX (Z_to_bv 64 (SIGMA CS_record))
    SUP_BROADCAST_STK (spZ regs) (sb_FP O) ly S W mem md [] ly S mdX 0
    RECORD_STK (sbb_rec_FP R O) (EV_RECORD R) (-32) (Z_to_bv 64 (BASE + SBB_RET_REC)) [] (sbb_rec_Q B MT ly S R O) HJ).
  - lia.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - etransitivity; [exact (RCS 3 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) | exact Hgp].
  - etransitivity; [exact (RCS 4 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) | exact Htp].
  - exact R1.
  - apply ret_ok_codeptr_v; [unfold SBB_RET_REC, AF_sup_broadcast; lia | reflexivity].
  - unfold SBB_RET_REC, AF_sup_broadcast. rewrite unsigned_lit_small by lia. lia.
  - apply achain_low. unfold s0Z. rewrite R8. unfold w64. rewrite unsigned_lit_small by lia.
    pose proof (req_size_pos kb ltac:(lia)) as [_ Hkr]. lia.
  - intros HPRE2. rewrite sbb_sig_record.
    eapply SRr_mono.
    { exact (TRECORD fx ly S W regsX memX mdX [] REC_BROADCAST R O HPRE2 HROD1 R10
        ltac:(unfold REC_BROADCAST, REC_FN_COUNT; lia) HREC1 HEVR HMOKR). }
    cbv beta. unfold apost_base. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HK2).
    exists ly2, S2, regs2, mem2, md2. split; [rewrite R1; reflexivity|]. split; [exact HJ2|]. split; [exact HP2 | exact HK2].
  - exact (sbb_rec_fp_ok ly S W mem md R O HAR HOb Hsl). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Hc & HJ2 & HJc & HP2 & HK2).
exists ly2, S2, regs2, mem2, md2. split; [exact Hc|]. split; [exact HJ2|]. split; [exact HJc|]. split; [exact HP2 | exact HK2].
Qed.

(* record's return (0x8b50c): the frame and the line survive the call, the recorder holds (5, []) in the slot *)
Lemma sbb_ret_rec_of : forall ly S W regs mem md ch pl line R O regsX memX mdX ly2 S2 (W2 : world SEGS) regs2 mem2 md2,
sbb_ent B MT ly S W regs mem md ch pl line R O ->
sbb_at_rec B ly S W regs mem md pl R O regsX memX mdX ->
ajournal SEGS B SUP_BROADCAST_STK (spZ regs) (sb_FP O) ly S W mem md [] ly2 S2 W2 mem2 md2 (0 + EV_RECORD R) ->
ajournal SEGS B RECORD_STK (spZ regs + -32) (sbb_rec_FP R O) ly S W memX mdX [] ly2 S2 W2 mem2 md2 (EV_RECORD R) ->
aregs_preserved regsX regs2 ->
sbb_rec_Q B MT ly S R O ly2 S2 W2 regs2 mem2 md2 ->
exists F O1, sbb_ret_rec B MT ly S W regs mem md pl line R O ly2 S2 W2 regs2 mem2 md2 F O1.
Proof.
intros ly S W regs mem md ch pl line R O regsX memX mdX ly2 S2 W2 regs2 mem2 md2 HENT HAT HJ2 HJc HP2 HK2.
destruct HENT as (HPRE & HFRM & Hfr8 & HROD & H10 & Hpl & HBLK & HAP & HSTR & HLEN & HREC & Hev & Hlive & HMOK).
destruct HAT as (HJ & Hsp & R1 & R8 & R10 & RCS & (Vra & Vs0 & Vs1) & KEEP & HROD1 & HREC1).
destruct HK2 as (F & O1 & Q10 & QP & QF & QFO & QREP & QO1 & QBB & QMLE).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJc as (HAR2 & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct sbb_stk as (WSTK & WREC & _).
assert (HOb : forall pn, In pn O -> In pn (ablocks B ly S)) by (intros pn Hpn; exact (proj2 (sbb_rep_pos B _ _ _ _ _ pn HREC Hpn))).
pose proof (sbb_rec_slot_ok ly S _ R O HREC) as Hsl. pose proof (sb_slot_range _ Hsl) as Hslr.
(* every byte of record's footprint lies below alloc_ceiling; its bytes outside the blocks are statics *)
assert (FPLOW : forall a, inFP (sbb_rec_FP R O) a -> a < alloc_ceiling).
{ intros a Ha. destruct (sbb_rec_fp_ok ly S W memX mdX R O (proj1 HJ) HOb Hsl a Ha) as [(_ & [(b & n & Hin & Hr) | (_ & Hi)]) | (b & n & Hin & _ & Hr)].
  - pose proof (sbb_blk ly S W mem md b n HAR Hin). lia.
  - pose proof (pa_segs_low a Hi). lia.
  - pose proof (sbb_blk ly S W mem md b n HAR Hin). lia. }
assert (HSO : ~ YI16.sink_open_fp (sbb_rec_FP R O)).
{ apply sink_closed_pos. unfold sbb_rec_FP. constructor; [cbn [fst]; unfold A_G_REC, OFF_NCALLS; lia|].
  constructor; [cbn [fst]; unfold A_G_REC in Hslr; lia|].
  destruct (Nat.ltb (length (r_calls R)) 16); [constructor|].
  unfold ablocks_fp. apply Forall_map. apply Forall_forall. intros [b m] Hin. cbn [fst].
  pose proof (sbb_blk ly S W mem md b m HAR (HOb _ Hin)). lia. }
(* the frame survives the call: above the callee's window, outside its footprint *)
assert (KF : forall a, spZ regs - 32 <= a < spZ regs -> rdW W2 mem2 a = rdW W memX a).
{ intros a Ha. apply G1; [lia | lia | intros Hf; pose proof (FPLOW a Hf); lia]. }
assert (E2 : getr regs2 2 = getr regsX 2) by exact (HP2 2 ltac:(unfold acallee_saved; lia)).
assert (E8 : getr regs2 8 = getr regsX 8) by exact (HP2 8 ltac:(unfold acallee_saved; lia)).
(* the line's block is none of the freed ones *)
destruct HBLK as (pb & kb & Hinb & Hpb1 & Hpb2).
destruct (sbb_blk ly S W mem md pb kb HAR Hinb) as (Hb4 & Hbc & Hkb & _ & Hkbr).
assert (Hinb2 : In (pb, kb) (ablocks B ly2 S2)).
{ pose proof (Permutation_in _ QP Hinb) as Hx. apply in_app_or in Hx as [Hx | Hx]; [exact Hx|].
  exfalso. pose proof (proj1 (Forall_forall _ _) HAP _ (QFO _ Hx)) as Hd. unfold iv_apart in Hd. cbn [fst snd] in Hd. lia. }
(* the line's bytes are kept: inside its block, apart from every block of O *)
assert (KL : forall j, 0 <= j < Z.of_nat (length line) + 1 -> rdW W2 mem2 (pl + j) = rdW W mem (pl + j)).
{ intros j Hj. replace (pl + j) with (pb + (pl - pb + j)) by lia.
  rewrite (G2 pb kb (pl - pb + j) Hinb Hinb2 ltac:(lia)).
  - rewrite KEEP by lia. reflexivity.
  - intros Hf. replace (pb + (pl - pb + j)) with (pl + j) in Hf by lia.
    unfold sbb_rec_FP in Hf. apply inFP_cons in Hf as [Hf | Hf].
    + apply (blk_img SEGS B LAWS ly S W mem md pb kb (pl + j) HAR Hinb ltac:(lia)).
      apply (cif_prog_img _ _ IMG). exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; unfold OFF_NCALLS in Hf; lia].
    + apply inFP_cons in Hf as [Hf | Hf].
      * apply (blk_img SEGS B LAWS ly S W mem md pb kb (pl + j) HAR Hinb ltac:(lia)).
        apply (cif_prog_img _ _ IMG). apply (sb_slot_pg (rec_slot R)); [exact Hsl | unfold CALL_SIZE; lia].
      * destruct (Nat.ltb (length (r_calls R)) 16); [exact (inFP_nil _ Hf)|].
        destruct (inFP_ablocks_fp_inv O _ Hf) as (b & m & Hin & Hr).
        pose proof (proj1 (Forall_forall _ _) HAP _ Hin) as Hd. unfold iv_apart in Hd. cbn [fst snd] in Hd.
        pose proof (proj1 (sbb_rep_pos B _ _ _ _ _ _ HREC Hin)) as Hm. cbn [snd] in Hm.
        assert (Erm : req_size m = m) by (unfold req_size; destruct (m =? 0) eqn:Em; [apply Z.eqb_eq in Em; lia | reflexivity]).
        rewrite Erm in Hr. lia. }
exists F, O1.
split; [rewrite Z.add_0_l in HJ2; exact HJ2|].
split; [unfold spZ; rewrite E2; exact Hsp|].
split; [rewrite E8; exact R8|]. split; [exact Q10|].
split; [intros r Hr H2' H8'; rewrite (HP2 r Hr); exact (RCS r Hr H2' H8')|].
split.
{ split; [|split]; intros kk Hkk; rewrite KF by (cbn in Hkk; lia); [exact (Vra kk Hkk) | exact (Vs0 kk Hkk) | exact (Vs1 kk Hkk)]. }
split.
{ intros a H1 H2 H3. destruct (sbb_ro_low a H1) as (Hi & Ha).
  rewrite (G3 a Hi H2 H3); [exact (HROD1 a H1 H2 H3)|].
  apply fp_spares_closed; [exact HSO|]. intros Hf.
  destruct (sbb_rec_fp_ok ly S W memX mdX R O (proj1 HJ) HOb Hsl a Hf) as [(_ & [(b & n & Hin & Hr) | (Hpg & _)]) | (b & n & Hin & _ & Hr)].
  - exact (blk_img SEGS B LAWS ly S W mem md b n a HAR Hin Hr Hi).
  - apply (cif_prog_not_ro _ _ IMG a); [|exact H1].
    rewrite (ts_prog B HB) in Hpg. unfold TFIB_PROG_STATIC in Hpg. apply Exists_exists in Hpg as (r & Hr & Hrr).
    unfold in_zr in Hrr. destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hrr;
    [exists (A_G_REC, A_G_REC + 960) | exists (A_REC_SPILL, A_REC_SPILL + 56) | exists (A_G_QUITTING, A_G_QUITTING + 4)];
    (split; [cbn [cmd_PG In]; tauto | cbn [fst snd]; unfold A_G_REC, A_REC_SPILL, A_G_QUITTING; lia]).
  - exact (blk_img SEGS B LAWS ly S W mem md b n a HAR Hin Hr Hi). }
split; [exact QREP|]. split; [exact QO1|]. split; [exact QP|]. split; [exact QFO|]. split; [exact QF|].
split; [exists pb, kb; split; [exact Hinb2 | lia]|].
split.
{ destruct HSTR as [HSb HSn]. split; [intros ii Hii | exact HSn].
  rewrite length_app in Hii; cbn [length] in Hii.
  rewrite KL by lia. exact (HSb ii ltac:(rewrite length_app; cbn [length]; lia)). }
split; [exact QBB | exact QMLE].
Qed.

End e.
End f.
End d.
