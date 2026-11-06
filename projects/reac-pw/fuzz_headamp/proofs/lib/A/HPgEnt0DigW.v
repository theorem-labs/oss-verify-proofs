(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACez.v, with its module paths and module names changed; 80 of its 105 lines of code are new or changed and 215 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0DigW.v at 97ea9c9eafa (its walk dg_walk);
   re-walked on image B's own code: image B's three runs (lib/AU/HPgE0DigK.v, lib/AU/HPgE0DigR.v), its registers,
   the frame of class 4 and its shadow row in HPgMem's hmu_sh words, and the R-cell R+0xc0 the pointer-overflow
   test reads. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgE0DigW.v, with its module paths, module names and numbers changed; 377 of its 436 lines of code are new or changed and 46 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0DigW.v at 97ea9c9eafa; for reac-pw/fuzz_headamp image A: module paths, the rs_ / rl_ / rm_ / RS_ / RM_ prefixes renamed to hs_ / hd_ / hm_ / HS_ / HM_; every pc moved by the code's uniform shift +0xd20 over [0x80a80, 0x81af0); the frame for locals of class 4 (1024 bytes, 128 shadow bytes); hm_sh's sixth scope flag (x) out of scope. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; addresses measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a): the walk of the DIG block of ent_build's
   case 0 (pod.h:237-246: the decimal digits of v = c mod 64 into r[4], reversed into ch with its NUL) from 0x81920 to
   G = 0x81a34, over the journal (no cut state). Proves no function (kind: segment lemma).

   THE CODE and how the walk cuts it:
     1  0x81920 .. 0x81930  a3 := 0, a4 := c & 63, r in scope (`sb` 4 into the frame's shadow byte 0x1c), a6 := 1
     2  0x81934 .. 0x81a28  the digits loop (one shadow check of r[n] per digit, the `% 10` by `mulhu`), the reverse
                            loop (the checks of r[n] and ch[j]), the NUL's check and store
     3  0x81a2c .. 0x81a30  r out of scope again (`sb` 0xf8 into the frame's shadow byte 0x1c)
   Runs 1 and 3 store a shadow byte, so they are plain engine runs (YCbq.v aj_run_to) with that byte as their only
   writable region; run 2 passes instrumented checks, so it is a token run (aj_run_to_tok) with the frame's shadow
   row out of the state and r and ch as its writable regions (their shadow entries say they are application memory).
   The engine keeps no range for a `mulhu` result, so run 2 is done once per value of v (0 .. 63) with v a literal:
   every branch is decided and every stored byte is a literal. Each run is entered from the semantic facts and left
   through HPgW7bBase.w7_post_of_run; dg_walk chains them. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgSteps HPgMem HPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgEnt0Def HPgW7bBase HPgEnt0OddW.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the entry states ---- *)
(* the highest address a frame for locals reaches (alloc_ceiling's bound, YCbq.v asan_consts) *)
Definition DG_FHI : Z := 0x7fffff800000.
(* run 2: r[4] (s6 = F + 0xe0) and ch[24] (s4 = F + 0xa0), both writable, 32-aligned *)
Definition dg_regions : smem :=
  [ YP09.mkRegion (Some 22%nat) 0 4 0 4 []; YP09.mkRegion (Some 20%nat) 0 24 0 24 [] ].
Definition dg_facts : facts := mkFacts
  [ (23%nat, mkAF W7SB W7SB 0); (22%nat, mkAF 4096 DG_FHI 5); (20%nat, mkAF 4096 DG_FHI 5) ] [] [].
Definition ss_dg2 : sstate := mkSS 0x81934 sr_atoms dg_regions None dg_facts.
Definition dg_SH : list shent := [mkSHE 22 4 0; mkSHE 20 24 0].
(* runs 1 and 3: the frame's shadow byte of r (granule 0x1c from s3 = shadow_addr F) *)
Definition ss_dgr (pc : Z) : sstate :=
  mkSS pc sr_atoms [YP09.mkRegion (Some 19%nat) 0x1c 0x1d 0x1c 0x1d []] None (mkFacts [] [] []).
(* what the block may change *)
Definition dg_clob : list (bv 5) := [10; 11; 12; 13; 14; 15; 16; 17]%bv.
Definition dg_wr (F : Z) : Z -> Prop :=
  fun a => (F + 0xa0 <= a < F + 0xb8) \/ (F + 0xe0 <= a < F + 0xe4) \/ a = shadow_addr F + 0x1c.
(* HPgEnt0Def.r7_tbl, computed once *)
Definition dg_tbl : ctable := Eval vm_compute in r7_tbl.
Lemma dg_tbl_ok : table_ok rsegs dg_tbl.
Proof.
assert (E : r7_tbl = dg_tbl) by (vm_compute; reflexivity). rewrite <- E. exact r7_tbl_ok.
Qed.

(* ---- reading literal bytes back out of a region's chunks ---- *)
Definition dg_lb (z : Z) : Z := bv_unsigned (YP09.byte_of_word (Z_to_bv 64 z) 0).
Definition dg_ck (o b : Z) (ck : YP09.chunk) : bool :=
  (YP09.c_off ck =? o) &&
  match YP09.c_val ck with CVal w (SLit z) => N.eqb w 1 && (dg_lb z =? b) | _ => false end.
Definition dg_has (cs : list YP09.chunk) (o0 : Z) (l : list byte) : bool :=
  forallb (fun i => existsb (dg_ck (o0 + Z.of_nat i) (bv_unsigned (nth i l (Z_to_bv 8 0)))) cs) (seq 0 (length l)).
Definition dg_reg_has (orr : option YP09.region) (k : nat) (o0 : Z) (l : list byte) : bool :=
  match orr with
  | Some r => match YP09.r_base r with Some k' => Nat.eqb k' k && dg_has (YP09.r_chunks r) o0 l | None => false end
  | None => false
  end.

(* every v in [0, n) from one goal per literal *)
Fixpoint dg_all (P : Z -> Prop) (n : nat) : Prop :=
  match n with O => True | S n' => dg_all P n' /\ P (Z.of_nat n') end.
Lemma dg_upto : forall (P : Z -> Prop) n, dg_all P n -> forall v, 0 <= v < Z.of_nat n -> P v.
Proof.
intros P n. induction n as [|n IH]; intros H v Hv; [lia|].
destruct H as [H1 H2]. destruct (Z.eq_dec v (Z.of_nat n)) as [->|Hne]; [exact H2|].
apply IH; [exact H1 | lia].
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma dg_bytes_of_st : forall E ss (H : word -> bool) ms i (k : nat) b o0 (l : list byte),
st_ok rsegs E ss (restrict H ms) -> dg_reg_has (nth_error (ss_mem ss) i) k o0 l = true ->
bv_unsigned (ew E k) = b -> hm_bytes rsegs H (ms_mem ms) (b + o0) l.
Proof.
intros E ss H ms i k b o0 l HS Hc Hb.
unfold dg_reg_has in Hc. destruct (nth_error (ss_mem ss) i) as [r|] eqn:Hn; [|discriminate].
destruct (YP09.r_base r) as [k'|] eqn:Hbase; [|discriminate].
apply andb_prop in Hc as [Hk Hc]. apply Nat.eqb_eq in Hk. subst k'.
pose proof (w7_region_nth E ss (restrict H ms) i r HS Hn) as Hok.
destruct Hok as (_ & _ & _ & Hcs).
apply hm_bytes_aview. intros j Hj.
unfold dg_has in Hc. rewrite forallb_forall in Hc.
specialize (Hc j ltac:(apply in_seq; lia)). apply existsb_exists in Hc as (ck & Hin & Hck).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hok. rewrite Hbase in Hok. cbn [base_val] in Hok. rewrite Hb in Hok.
destruct ck as [off cv]. unfold dg_ck in Hck. cbn [YP09.c_off YP09.c_val] in Hck, Hok.
apply andb_prop in Hck as [Ho Hv]. apply Z.eqb_eq in Ho.
destruct cv as [w e | | |]; try discriminate.
destruct e; try discriminate.
apply andb_prop in Hv as [Hw Hz]. apply N.eqb_eq in Hw. apply Z.eqb_eq in Hz. subst w off.
destruct (Hok 0 ltac:(cbn; lia)) as (bt & E1 & E2).
cbn [YP09.cbyte YP09.c_off YP09.c_val sv_denot] in E1, E2. injection E1 as <-.
unfold aview. replace (b + o0 + Z.of_nat j) with (b + (o0 + Z.of_nat j) + 0) by lia.
change (ms_mem (restrict H ms)) with (mrestrict H (ms_mem ms)) in E2.
rewrite E2. cbn [option_map]. f_equal. exact Hz.
Qed.

(* every register outside clob keeps its value: its symbolic value is still its own atom, or the literal it was
   pinned to at the run's entry (HPgW7bBase.w7_regs_kept with pins) *)
Lemma dg_regs_kept : forall E ss ms regs0 extra (H : word -> bool) (clob : list (bv 5)) (pins : list (bv 5 * Z)),
st_ok rsegs E ss (restrict H ms) -> env_agree 32 (Ereg regs0 extra) E ->
Forall (fun p => getr regs0 (fst p) = Z_to_bv 64 (snd p)) pins ->
forallb (fun r : bv 5 => existsb (fun c => bv_eqb c r) clob
  || sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)
  || existsb (fun p => bv_eqb (fst p) r && sv_eqb (sr_get (ss_regs ss) r) (SLit (snd p))) pins) w7_nz_regs = true ->
forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr (ms_regs ms) r = getr regs0 r.
Proof.
intros E ss ms regs0 extra H clob pins HS [HA _] Hp Hck r Hr0 Hn.
pose proof (proj1 (forallb_forall _ _) Hck r (w7_in_nz_regs r Hr0)) as Hq. cbn beta in Hq.
apply orb_prop in Hq as [Hq|Hq]; [apply orb_prop in Hq as [Hq|Hq]|].
- exfalso. apply existsb_exists in Hq as (c & Hc & Hb). apply bv_eqb_eq in Hb. subst c. exact (Hn Hc).
- apply sv_eqb_eq in Hq.
  rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hq. cbn [sv_denot]. rewrite Z.add_0_r.
  rewrite HA. 2:{ pose proof (u5_range r). lia. }
  rewrite ew_Ereg_reg, Z_to_bv_bv_unsigned. reflexivity.
- apply existsb_exists in Hq as ([q z] & Hin & Hb). apply andb_prop in Hb as [Hb1 Hb2].
  apply bv_eqb_eq in Hb1. apply sv_eqb_eq in Hb2. cbn [fst snd] in Hb1, Hb2. subst q.
  rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hb2. cbn [sv_denot].
  rewrite Forall_forall in Hp. specialize (Hp (r, z) Hin). cbn [fst snd] in Hp. rewrite Hp. reflexivity.
Qed.

Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.

(* the frame for locals of the block's journal: 32-aligned, its bytes and its shadow bytes present *)
Lemma dg_frame : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k F pos,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
In (4, pos) own -> F = frame_addr lyc 4 pos ->
F mod 32 = 0 /\ 4096 <= F /\ F + 1024 <= DG_FHI /\ in_app F 1024 /\
(forall a, F <= a < F + 1024 -> apresent (w_H W) memc a) /\
(forall i, 0 <= i < 128 -> apresent (w_H W) memc (shadow_addr F + i)).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k F pos HJ Hown HF.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin3 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin3) as (HF32 & HFapp & HFpres & HFsh).
destruct (frames_bounds rsegs B LAWS lyc Sc W memc mdc 4 pos HAR Hin3) as (HF4096 & HFceil & _).
rewrite <- HF in HF32, HFapp, HFpres, HFsh, HF4096, HFceil.
change (fs_frame_bytes 4) with 1024 in HFapp, HFpres, HFsh, HFceil.
pose proof asan_consts as (C1 & _).
split; [exact HF32|]. split; [exact HF4096|]. split; [unfold DG_FHI; lia|]. split; [exact HFapp|].
split; [intros a Ha; exact (proj1 (HFpres a Ha))|].
intros i Hi. exact (proj1 (HFsh i ltac:(change (1024 / 8) with 128; lia))).
Qed.

(* an awr_ok window inside the frame for locals or its shadow row *)
Lemma dg_awr_frame : forall STK sp0 FP bl0 blc lyc own F pos a,
In (4, pos) own -> F = frame_addr lyc 4 pos ->
(F <= a < F + 1024 \/ shadow_addr F <= a < shadow_addr F + 128) ->
awr_byte STK sp0 FP bl0 blc lyc own a.
Proof.
intros STK sp0 FP bl0 blc lyc own F pos a Hown HF Ha.
right; right; right. exists 4, pos. split; [exact Hown|]. unfold in_zr. cbn [fst snd]. rewrite <- HF.
change (fs_frame_bytes 4) with 1024. change (1024 / 8) with 128. destruct Ha as [Ha|Ha]; [left | right]; lia.
Qed.

Lemma dg_F8 : forall F, F mod 32 = 0 -> F mod 8 = 0.
Proof.
intros F H. apply Z.mod_divide in H; [|lia]. destruct H as [z Hz]. rewrite Hz.
replace (z * 32) with ((4 * z) * 8) by lia. apply Z.mod_mul. lia.
Qed.

Lemma dg_sh_bounds : forall F, 4096 <= F -> F + 1024 <= DG_FHI ->
SHADOW_OFF + 512 <= shadow_addr F /\ shadow_addr F + 128 <= SHADOW_OFF + 2 ^ 44.
Proof.
intros F H0 H1. unfold shadow_addr, SHADOW_OFF, DG_FHI in *.
assert (D0 : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (D1 : F / 8 <= 17592186044288) by (apply Z.div_le_upper_bound; lia).
change (2 ^ 44) with 17592186044416. lia.
Qed.

(* ======================== run 1: 0x81920 -> 0x81934 ======================== *)
Lemma dg_run1 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) F pos c,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
In (4, pos) own -> F = frame_addr lyc 4 pos ->
getr regs 19 = w64 (shadow_addr F) -> getr regs 10 = w64 c -> 0 <= c < 256 ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 0x81920) memc (seg_rom rsegs)) mdc)
(w7_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k 0x81934 regs memc mdc [10; 13; 14; 16]%bv
  (fun a => a = shadow_addr F + 0x1c)
  (fun regs2 mem2 => getr regs2 13 = w64 0 /\ getr regs2 14 = w64 (c mod 64) /\ getr regs2 16 = w64 1 /\
     aview rsegs (w_H W) mem2 (shadow_addr F + 0x1c) = Some 4)).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs F pos c HJ Hown HF H19 H10 Hc.
pose proof w7_wx as Hwx. pose proof w7_segs_low as Hsegs.
destruct (dg_frame STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k F pos HJ Hown HF)
  as (HF32 & HF4096 & HFhi & HFapp & HFpres & HFsh).
pose proof (dg_sh_bounds F HF4096 HFhi) as (SB0 & SB1).
assert (B19 : bv_unsigned (ew (Ereg regs []) 19) = shadow_addr F)
  by (rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl), H19; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
assert (E10 : ew (Ereg regs []) 10 = Z_to_bv 64 c) by (rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (HS : st_ok rsegs (Ereg regs []) (ss_dgr 0x81920)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x81920) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (hm_rw_region rsegs _ (w_H W) memc 19%nat (shadow_addr F) 0x1c 0x1d 0x1c 0x1d []);
      [exact B19 | unfold SHADOW_OFF in *; lia | unfold SHADOW_OFF in *; lia | | constructor].
    intros o Ho. apply HFsh. lia.
  - cbn. tauto.
  - split; [|split; exact I]. cbn. exact I. }
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
aj_run_to dg_tbl_ok HS HJ 0x81934.
- eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat (shadow_addr F)); [reflexivity | exact B19 | | apply awr_ok_nil].
  cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply (dg_awr_frame _ _ _ _ _ _ _ F pos a Hown HF). right. lia.
- eapply (w7_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply same_io_wvb | | | exact HG | ].
  + eapply (w7_regs_kept _ _ ms regs [] (w_H W) _ HS); [exact HAE | vm_compute; reflexivity].
  + intros a Ha Hz. eapply (kept_run (fun a => a = shadow_addr F + 0x1c) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr); [ | exact Ha | exact Hz].
    intros x (r & Hr & Hb). cbn [ss_dgr ss_mem In] in Hr. destruct Hr as [<-|[]].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb. rewrite B19 in Hb. lia.
  + split; [|split; [|split]].
    * o_reg HS (13%bv : bv 5). reflexivity.
    * o_reg HS (14%bv : bv 5). rewrite denot_lit_U. unfold w64. f_equal.
      rewrite U_SAlu, U_SLit, (U_atom _ 10 c E10) by lia. cbn [zalu_raw].
      change (zcanon 63) with 63.
      replace (Z.land c 63) with (c mod 64) by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; reflexivity).
      apply zcanon_id. pose proof (Z.mod_pos_bound c 64 ltac:(lia)). unfold M64. lia.
    * o_reg HS (16%bv : bv 5). reflexivity.
    * pose proof (dg_bytes_of_st _ _ (w_H W) ms 0 19 (shadow_addr F) 0x1c [Z_to_bv 8 4] HS
        ltac:(vm_compute; reflexivity) B19) as Hb.
      pose proof (proj1 (hm_bytes_aview rsegs _ _ _ _) Hb 0%nat ltac:(cbn; lia)) as Ha.
      rewrite Z.add_0_r in Ha. exact Ha.
Qed.

(* ======================== run 3: 0x81a2c -> G 0x81a34 ======================== *)
Lemma dg_run3 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) F pos,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
In (4, pos) own -> F = frame_addr lyc 4 pos ->
getr regs 19 = w64 (shadow_addr F) ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 0x81a2c) memc (seg_rom rsegs)) mdc)
(w7_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k 0x81a34 regs memc mdc [10]%bv
  (fun a => a = shadow_addr F + 0x1c)
  (fun _ mem2 => aview rsegs (w_H W) mem2 (shadow_addr F + 0x1c) = Some 0xf8)).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs F pos HJ Hown HF H19.
pose proof w7_wx as Hwx. pose proof w7_segs_low as Hsegs.
destruct (dg_frame STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k F pos HJ Hown HF)
  as (HF32 & HF4096 & HFhi & HFapp & HFpres & HFsh).
pose proof (dg_sh_bounds F HF4096 HFhi) as (SB0 & SB1).
assert (B19 : bv_unsigned (ew (Ereg regs []) 19) = shadow_addr F)
  by (rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl), H19; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
assert (HS : st_ok rsegs (Ereg regs []) (ss_dgr 0x81a2c)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x81a2c) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (hm_rw_region rsegs _ (w_H W) memc 19%nat (shadow_addr F) 0x1c 0x1d 0x1c 0x1d []);
      [exact B19 | unfold SHADOW_OFF in *; lia | unfold SHADOW_OFF in *; lia | | constructor].
    intros o Ho. apply HFsh. lia.
  - cbn. tauto.
  - split; [|split; exact I]. cbn. exact I. }
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
aj_run_to dg_tbl_ok HS HJ 0x81a34.
- eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat (shadow_addr F)); [reflexivity | exact B19 | | apply awr_ok_nil].
  cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply (dg_awr_frame _ _ _ _ _ _ _ F pos a Hown HF). right. lia.
- eapply (w7_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply same_io_wvb | | | exact HG | ].
  + eapply (w7_regs_kept _ _ ms regs [] (w_H W) _ HS); [exact HAE | vm_compute; reflexivity].
  + intros a Ha Hz. eapply (kept_run (fun a => a = shadow_addr F + 0x1c) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr); [ | exact Ha | exact Hz].
    intros x (r & Hr & Hb). cbn [ss_dgr ss_mem In] in Hr. destruct Hr as [<-|[]].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb. rewrite B19 in Hb. lia.
  + pose proof (dg_bytes_of_st _ _ (w_H W) ms 0 19 (shadow_addr F) 0x1c [Z_to_bv 8 0xf8] HS
      ltac:(vm_compute; reflexivity) B19) as Hb.
    pose proof (proj1 (hm_bytes_aview rsegs _ _ _ _) Hb 0%nat ltac:(cbn; lia)) as Ha.
    rewrite Z.add_0_r in Ha. exact Ha.
Qed.

(* ======================== run 2: 0x81934 -> 0x81a2c, one literal v at a time ======================== *)
(* an obligation of run 2: a byte of r or of ch is addressable *)
Ltac dg_obl HoR HoC := first [ refine (HoR _ _); lia | refine (HoC _ _); lia ].
(* a token run's last environment agrees with its first below 32: it only sets the fresh atoms K, K + 1, ... *)
Lemma dg_agree_step : forall E0 E k w, env_agree 32 E0 E -> (32 <= k)%nat -> env_agree 32 E0 (ewset E k w).
Proof.
intros E0 E k w [HA HD] Hk. split; [|exact HD].
intros n Hn. rewrite ew_ewset_other by lia. exact (HA n Hn).
Qed.
Ltac dg_agree HAE := first [ exact HAE | apply dg_agree_step; [dg_agree HAE | apply Nat.leb_le; reflexivity] ].

Lemma dg_run2 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) F pos v,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
In (4, pos) own -> F = frame_addr lyc 4 pos ->
getr regs 23 = w64 SHADOW_OFF -> getr regs 22 = w64 (F + 0xe0) -> getr regs 20 = w64 (F + 0xa0) ->
getr regs 13 = w64 0 -> getr regs 16 = w64 1 -> getr regs 17 = w64 10 -> getr regs 5 = w64 9 ->
getr regs 18 = w64 HS_MULT10 -> getr regs 14 = w64 v -> 0 <= v < 64 ->
hd_fsh rsegs (w_H W) memc F (hm_sh true true true true false false) ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 0x81934) memc (seg_rom rsegs)) mdc)
(w7_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k 0x81a2c regs memc mdc dg_clob
  (fun a => (F + 0xa0 <= a < F + 0xb8) \/ (F + 0xe0 <= a < F + 0xe4))
  (fun _ mem2 => hm_bytes rsegs (w_H W) mem2 (F + 0xa0) (dec64 v ++ [NUL]))).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs F pos v
  HJ Hown HF H23 H22 H20 H13 H16 H17 H5 H18 H14 Hv Hfsh.
pose proof w7_wx as Hwx. pose proof w7_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin3 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (dg_frame STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k F pos HJ Hown HF)
  as (HF32 & HF4096 & HFhi & HFapp & HFpres & HFsh).
pose proof (dg_F8 F HF32) as HF8.
assert (A22 : (F + 0xe0) mod 32 = 0) by (rewrite Z.add_mod, HF32 by lia; reflexivity).
assert (A20 : (F + 0xa0) mod 32 = 0) by (rewrite Z.add_mod, HF32 by lia; reflexivity).
assert (E22 : ew (Ereg regs []) 22 = Z_to_bv 64 (F + 0xe0)) by (rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (E20 : ew (Ereg regs []) 20 = Z_to_bv 64 (F + 0xa0)) by (rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
assert (E23 : ew (Ereg regs []) 23 = Z_to_bv 64 SHADOW_OFF) by (rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact H23).
assert (B22 : bv_unsigned (ew (Ereg regs []) 22) = F + 0xe0)
  by (rewrite E22; apply unsigned_lit_small; unfold DG_FHI in HFhi; lia).
assert (B20 : bv_unsigned (ew (Ereg regs []) 20) = F + 0xa0)
  by (rewrite E20; apply unsigned_lit_small; unfold DG_FHI in HFhi; lia).
(* the entry state, with the loop's constants pinned to literals *)
assert (HS0 : st_ok rsegs (Ereg regs []) ss_dg2
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x81934) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + apply (hm_rw_region rsegs _ (w_H W) memc 22%nat (F + 0xe0) 0 4 0 4 []);
        [exact B22 | lia | unfold DG_FHI in HFhi; lia | | constructor].
      intros o Ho. apply HFpres. lia.
    + apply (hm_rw_region rsegs _ (w_H W) memc 20%nat (F + 0xa0) 0 24 0 24 []);
        [exact B20 | lia | unfold DG_FHI in HFhi; lia | | constructor].
      intros o Ho. apply HFpres. lia.
  - cbn [pairwise_disjoint all_disjoint dg_regions]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite B22, B20.
    split; [split; [right; lia | exact I] | split; exact I].
  - split; [|split; exact I].
    cbn [ss_dg2 dg_facts f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
    rewrite E23, B22, B20. unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 0) with 1. change (2 ^ 5) with 32. rewrite Z.mod_1_r, A22, A20.
    unfold SHADOW_OFF, W7SB, DG_FHI in *. repeat split; lia. }
pose proof (st_ok_pin_lit rsegs _ _ _ 13%bv 0 HS0 eq_refl H13) as HS1.
pose proof (st_ok_pin_lit rsegs _ _ _ 16%bv 1 HS1 eq_refl H16) as HS2.
pose proof (st_ok_pin_lit rsegs _ _ _ 17%bv 10 HS2 eq_refl H17) as HS3.
pose proof (st_ok_pin_lit rsegs _ _ _ 5%bv 9 HS3 eq_refl H5) as HS4.
pose proof (st_ok_pin_lit rsegs _ _ _ 18%bv HS_MULT10 HS4 eq_refl H18) as HS5.
clear HS0 HS1 HS2 HS3 HS4.
(* what every value's run shares *)
assert (SHOK : sh_ok rsegs W7Bx dg_SH (Ereg regs []) (mrestrict (w_H W) memc)).
{ unfold dg_SH. constructor; [|constructor; [|constructor]].
  - apply (shent_app_of_frame rsegs B LAWS lyc Sc W memc mdc (Ereg regs []) W7Bx 22 (F + 0xe0) 4 pos 0 4 _ HAR Hin3).
    + unfold W7Bx. apply (U_atom _ 23 SHADOW_OFF E23). unfold SHADOW_OFF; lia.
    + rewrite U_SOff, B22, Z.add_0_r. apply zcanon_id. unfold M64, DG_FHI in *; lia.
    + rewrite <- HF; lia.
    + lia.
    + rewrite <- HF; change (fs_frame_bytes 4) with 1024; lia.
  - apply (shent_app_of_frame rsegs B LAWS lyc Sc W memc mdc (Ereg regs []) W7Bx 20 (F + 0xa0) 4 pos 0 24 _ HAR Hin3).
    + unfold W7Bx. apply (U_atom _ 23 SHADOW_OFF E23). unfold SHADOW_OFF; lia.
    + rewrite U_SOff, B20, Z.add_0_r. apply zcanon_id. unfold M64, DG_FHI in *; lia.
    + rewrite <- HF; lia.
    + lia.
    + rewrite <- HF; change (fs_frame_bytes 4) with 1024; lia. }
assert (Hawr : awr_ok (Ereg regs []) dg_regions STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own).
{ unfold dg_regions.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 22%nat (F + 0xe0)); [reflexivity | exact B22 | | ].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply (dg_awr_frame _ _ _ _ _ _ _ F pos a Hown HF). left. lia. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 20%nat (F + 0xa0)); [reflexivity | exact B20 | | apply awr_ok_nil].
  cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply (dg_awr_frame _ _ _ _ _ _ _ F pos a Hown HF). left. lia. }
assert (Hkwr : forall a, in_wrange (Ereg regs []) dg_regions a ->
  (F + 0xa0 <= a < F + 0xb8) \/ (F + 0xe0 <= a < F + 0xe4)).
{ intros a (r & Hr & Hb). cbn [dg_regions In] in Hr.
  destruct Hr as [<-|[<-|[]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
  rewrite ?B22, ?B20 in Hb; lia. }
assert (HoR : forall j, 0 <= j < 4 ->
  ob_holds rsegs W7Bx (Ereg regs []) (mrestrict (w_H W) memc) (mkOB (SOff 22 j) 1)).
{ intros j Hj. unfold ob_holds; cbn [ob_x ob_n]. unfold W7Bx.
  rewrite (U_atom _ 23 SHADOW_OFF E23) by (unfold SHADOW_OFF; lia).
  rewrite U_SOff, B22, zcanon_id by (unfold M64, DG_FHI in *; lia).
  replace (F + 0xe0 + j) with (F + HM_R + j) by (unfold HM_R; lia).
  exact (hm_A_ra_r rsegs _ _ F true true true false false j 1 Hfsh HF8 ltac:(lia) ltac:(lia)). }
assert (HoC : forall j, 0 <= j < 24 ->
  ob_holds rsegs W7Bx (Ereg regs []) (mrestrict (w_H W) memc) (mkOB (SOff 20 j) 1)).
{ intros j Hj. unfold ob_holds; cbn [ob_x ob_n]. unfold W7Bx.
  rewrite (U_atom _ 23 SHADOW_OFF E23) by (unfold SHADOW_OFF; lia).
  rewrite U_SOff, B20, zcanon_id by (unfold M64, DG_FHI in *; lia).
  replace (F + 0xa0 + j) with (F + HM_CH + j) by (unfold HM_CH; lia).
  exact (hm_A_ra_ch rsegs _ _ F true true true false false j 1 Hfsh HF8 ltac:(lia) ltac:(lia)). }
assert (Hpins : Forall (fun p : bv 5 * Z => getr regs (fst p) = Z_to_bv 64 (snd p)) [(5%bv, 9); (18%bv, HS_MULT10)])
  by (repeat constructor; assumption).
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
clear - HS5 HJ SHOK Hawr Hkwr HoR HoC Hpins HAE B20 Hwx Hsegs LAWS Hv H14.
(* one run per value of v *)
revert H14. pattern v. apply (dg_upto _ 64); [|exact Hv].
cbn [dg_all]. repeat split.
all: intros H14;
  lazymatch type of H14 with getr _ _ = w64 ?z =>
    pose proof (st_ok_pin_lit rsegs _ _ _ 14%bv z HS5 eq_refl H14) as HS end;
  aj_run_to_tok dg_tbl_ok HS HJ SHOK W7Bspan 0x81a2c;
  lazymatch goal with
  | |- range_addressable _ _ _ _ => dg_obl HoR HoC
  | |- awr_ok _ _ _ _ _ _ _ _ _ => exact Hawr
  | |- SRr _ _ _ _ =>
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
      assert (HA' : env_agree 32 (Ereg regs []) Ev) by dg_agree HAE end;
    eapply (w7_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply same_io_wvb | | | exact HG | ];
    [ eapply (dg_regs_kept _ _ ms regs [] (w_H W) _ _ HS); [exact HA' | exact Hpins | vm_compute; reflexivity]
    | intros a Ha Hz; eapply (kept_run _ _ _ (w_H W) memc memc (ms_mem ms) (fun a _ _ => eq_refl) HFr);
      [exact Hkwr | exact Ha | exact Hz]
    | rewrite <- (Z.add_0_r (F + 0xa0));
      apply (dg_bytes_of_st _ _ (w_H W) ms 1 20 (F + 0xa0) 0 _ HS);
      [ vm_compute; reflexivity | rewrite (proj1 HA' 20%nat ltac:(lia)); exact B20 ] ]
  end.
Qed.

(* ======================== the walk ======================== *)
(* a byte of an application range is not a shadow byte of the frame for locals *)
Lemma dg_app_not_sh : forall lo len a F, in_app lo len -> lo <= a < lo + len -> 4096 <= F -> F + 1024 <= DG_FHI ->
a <> shadow_addr F + 0x1c.
Proof.
intros lo len a F Happ Ha HF0 HF1 Heq. pose proof (dg_sh_bounds F HF0 HF1) as (SB0 & SB1).
revert SB0 SB1 Happ Ha Heq. unfold SHADOW_OFF. generalize (shadow_addr F). intros s SB0 SB1 Happ Ha Heq.
change (2 ^ 44) with 17592186044416 in SB1. zlia.
Qed.

Lemma dg_walk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k (regs : bvmap 5 word) F pos c,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
In (4, pos) own -> F = frame_addr lyc 4 pos ->
getr regs 19 = w64 (shadow_addr F) -> getr regs 23 = w64 SHADOW_OFF -> getr regs 22 = w64 (F + 0xe0) ->
getr regs 20 = w64 (F + 0xa0) -> getr regs 18 = w64 HS_MULT10 -> getr regs 10 = w64 c ->
getr regs 17 = w64 10 -> getr regs 5 = w64 9 -> 0 <= c < 256 ->
hd_fsh rsegs (w_H W) mem F (hm_sh true true false true false false) ->
SRr rsegs W (cfg_at rsegs R7_DIG regs mem md)
(w7_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k 0x81a34 regs mem md dg_clob (dg_wr F)
  (fun _ mem2 => hm_bytes rsegs (w_H W) mem2 (F + 0xa0) (dec64 (c mod 64) ++ [NUL]) /\
     aview rsegs (w_H W) mem2 (shadow_addr F + 0x1c) = Some 0xf8)).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k regs F pos c
  HJ Hown HF H19 H23 H22 H20 H18 H10 H17 H5 Hc Hfsh.
destruct (dg_frame STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k F pos HJ Hown HF)
  as (HF32 & HF4096 & HFhi & HFapp & _ & _).
pose proof (dg_sh_bounds F HF4096 HFhi) as (SB0 & SB1).
(* ---- run 1 ---- *)
eapply SRr_bind.
{ unfold cfg_at, w64. exact (dg_run1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k regs F pos c HJ Hown HF H19 H10 Hc). }
intros W1 c1 _ (-> & r1 & m1 & d1 & -> & HJ1 & Hio1 & Hk1 & Hm1 & Hp1 & R13 & R14 & R16 & R1sh).
assert (Hfsh1 : hd_fsh rsegs (w_H W) m1 F (hm_sh true true true true false false)).
{ rewrite <- (hm_sh_r_in true true false true false false).
  apply (hm_fsh_set rsegs (w_H W) mem (w_H W) m1 F _ 28 1 4 Hfsh).
  - intros i Hi. replace i with 0x1c by lia. exact R1sh.
  - intros i Hi Hn. rewrite hm_sh_len in Hi. apply Hm1; [unfold SHADOW_OFF in *; lia | lia]. }
(* ---- run 2 ---- *)
eapply SRr_bind.
{ refine (dg_run2 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m1 d1 k r1 F pos (c mod 64) HJ1 Hown HF
    _ _ _ R13 R16 _ _ _ R14 _ Hfsh1).
  - o_keep Hk1. exact H23.
  - o_keep Hk1. exact H22.
  - o_keep Hk1. exact H20.
  - o_keep Hk1. exact H17.
  - o_keep Hk1. exact H5.
  - o_keep Hk1. exact H18.
  - apply Z.mod_pos_bound. lia. }
intros W2 c2 _ (-> & r2 & m2 & d2 & -> & HJ2 & Hio2 & Hk2 & Hm2 & Hp2 & R2ch).
(* ---- run 3 ---- *)
eapply SRr_mono.
{ refine (dg_run3 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m2 d2 k r2 F pos HJ2 Hown HF _).
  rewrite (Hk2 19%bv ltac:(vm_compute; discriminate) ltac:(unfold dg_clob; o_notin)). o_keep Hk1. exact H19. }
intros W3 c3 _ (-> & r3 & m3 & d3 & -> & HJ3 & Hio3 & Hk3 & Hm3 & Hp3 & R3sh).
split; [reflexivity|]. exists r3, m3, d3.
split; [reflexivity|]. split; [exact HJ3|].
split; [eapply same_io_trans; [exact Hio1|]; eapply same_io_trans; [exact Hio2 | exact Hio3]|].
split.
{ intros r Hr0 Hn. unfold dg_clob in Hn. cbn [In] in Hn.
  rewrite (Hk3 r Hr0 ltac:(cbn [In]; tauto)), (Hk2 r Hr0 ltac:(unfold dg_clob; cbn [In]; tauto)),
    (Hk1 r Hr0 ltac:(cbn [In]; tauto)).
  reflexivity. }
split.
{ intros a Ha Hn. unfold dg_wr in Hn.
  rewrite (Hm3 a Ha ltac:(tauto)), (Hm2 a Ha ltac:(tauto)), (Hm1 a Ha ltac:(tauto)). reflexivity. }
split; [intros a Hpa; apply Hp3, Hp2, Hp1, Hpa|].
split; [|exact R3sh].
eapply (hm_bytes_kept rsegs); [exact R2ch|]. intros x Hx.
pose proof (dec64_len (c mod 64)) as Hl. rewrite length_app in Hx. cbn [length] in Hx.
apply Hm3; [unfold DG_FHI in HFhi; lia|].
apply (dg_app_not_sh F 1024 x F HFapp); [lia | exact HF4096 | exact HFhi].
Qed.
End d.
End b.
