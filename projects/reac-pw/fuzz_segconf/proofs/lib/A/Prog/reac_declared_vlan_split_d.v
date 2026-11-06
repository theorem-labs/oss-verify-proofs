(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:180-183, 357-361,
   for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue.v, with its module paths and numbers changed; 204 of its 254 lines of code are new or changed and 319 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/check_ignore.v, with its module names changed; 201 of its 235 lines of code are new or changed and 220 lines of the source are left out. *)
(* reac_declared_vlan_split on fuzz_segconf image A: the interface of its walk's segments. The walk is a chain of
   program points, each stated over the CONCRETE machine state there (registers, memory, model), as fuzz_command's
   LLVMFuzzerTestOneInput_s43.v states its loop head; each segment lemma seeds a fresh symbolic state from that
   concrete state (vs_seedK: the 64-byte frame with the eight saved registers, s6 = the shadow base), runs to the
   next point and applies that point's statement.

   Points (listing offsets from BASE; AF_reac_declared_vlan_split = 0x4e58 = image A 0x89b8c):
     K1 0x4eb8 (0x89bec) after the strrchr wrapper      KL 0x4ef0 (0x89c24) the head of the digit loop
     K2 0x4f2c (0x89c60) the strtol set-up             K3 0x4f38 (0x89c6c) after the strtol wrapper
     K4 0x4f9c (0x89cd0) after the strlen wrapper       K5 0x4fb8 (0x89cec) after the checked memcpy
     K6 0x4fd8 (0x89d0c) after name_ok                  KR 0x4f54 (0x89c88) the epilogue, a0 set.
   The walk proves reac_declared_vlan_split_contract itself (lib/A/Prog/reac_declared_vlan_split_c.v); the vid
   cell's real-stack arm carries astack_pres (SegABase.sa_dst), which name_ok's achain of s0 = vid needs at its
   call, 0x89d08. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YG0p YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_declared_vlan_split_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_declared_vlan_split_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition VS_K1 : Z := 0x4eb8.
Definition VS_KL : Z := 0x4ef0.
Definition VS_K2 : Z := 0x4f2c.
Definition VS_K3 : Z := 0x4f38.
Definition VS_K4 : Z := 0x4f9c.
Definition VS_K5 : Z := 0x4fb8.
Definition VS_K6 : Z := 0x4fd8.
Definition VS_KR : Z := 0x4f54.

(* the frame after the prologue, below the entry sp sp0: s6 s5 s4 s3 s2 s1 s0 ra at sp0 - 64 .. sp0 - 8, as atoms
   39 .. 32 of a seeded state (the entry values, its extra words vs_xs) *)
Definition vs_slots_r : YP09.region := YP09.mkRegion (Some 2%nat) 0 64 0 0
  [YP09.mkChunk 0 (CVal 8 (SOff 39 0)); YP09.mkChunk 8 (CVal 8 (SOff 38 0)); YP09.mkChunk 16 (CVal 8 (SOff 37 0));
   YP09.mkChunk 24 (CVal 8 (SOff 36 0)); YP09.mkChunk 32 (CVal 8 (SOff 35 0)); YP09.mkChunk 40 (CVal 8 (SOff 34 0));
   YP09.mkChunk 48 (CVal 8 (SOff 33 0)); YP09.mkChunk 56 (CVal 8 (SOff 32 0))].
Definition vs_saved : list (bv 5) := [1%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv].
Definition vs_xs (regs : bvmap 5 word) : list word := map (getr regs) vs_saved.
(* the seeded state at listing offset pc: the registers as their atoms, the frame, sp and s6 = SB known, and the
   point's own facts fs on further atoms *)
Definition vs_ssK (pc : Z) (fs : list (nat * afact)) : sstate :=
  mkSS pc sr_atoms [vs_slots_r] None (mkFacts ((2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: (22%nat, mkAF SB SB 0) :: fs) [] []).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the eight saved words of the frame, at sp0 - 64 .. sp0 - 8 *)
Definition vs_slots (rd : reader) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
  forall i r, nth_error vs_saved i = Some r ->
  rdword rd (sp0 - 8 - 8 * Z.of_nat i) = Some (bv_unsigned (getr regs r)).

Lemma vs_xs_nth : forall (regs : bvmap 5 word) ys i r, nth_error vs_saved i = Some r ->
  nth i (vs_xs regs ++ ys) (Z_to_bv 64 0) = getr regs r.
Proof.
intros regs ys i r H. assert (Hi : (i < length vs_saved)%nat) by (apply nth_error_Some; rewrite H; discriminate).
unfold vs_xs. rewrite app_nth1 by (rewrite length_map; exact Hi).
apply nth_error_nth. rewrite nth_error_map, H. reflexivity.
Qed.
Lemma vs_Ex : forall (regs' regs : bvmap 5 word) ys i r, nth_error vs_saved i = Some r ->
  ew (Eimg (Ereg regs' (vs_xs regs ++ ys))) (32 + i) = getr regs r.
Proof.
intros regs' regs ys i r H.
assert (Hi : (i < length vs_saved)%nat) by (apply nth_error_Some; rewrite H; discriminate). cbn [length vs_saved] in Hi.
rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. apply vs_xs_nth. exact H.
Qed.
Lemma vs_Exn : forall (regs' regs : bvmap 5 word) ys n i r, n = (32 + i)%nat -> nth_error vs_saved i = Some r ->
  ew (Eimg (Ereg regs' (vs_xs regs ++ ys))) n = getr regs r.
Proof. intros regs' regs ys n i r -> H. exact (vs_Ex regs' regs ys i r H). Qed.
Lemma vs_Ey : forall (regs' regs : bvmap 5 word) ys j, (j < 100)%nat ->
  ew (Eimg (Ereg regs' (vs_xs regs ++ ys))) (40 + j) = nth j ys (Z_to_bv 64 0).
Proof.
intros regs' regs ys j Hj. rewrite Eimg_low by (unfold A_TEXT; lia).
replace (40 + j)%nat with (32 + (8 + j))%nat by lia. rewrite ew_Ereg_extra.
rewrite app_nth2; unfold vs_xs; rewrite length_map; cbn [length vs_saved]; [|lia].
f_equal. lia.
Qed.
(* a seeded state after the prologue: the frame with the eight saved words, sp, s6 = SB, and the point's facts fs over
   the atoms of the registers and of the extra words ys (atoms 40, 41, ...) *)
Lemma vs_seedK : forall (W : world SEGS) (regs regs' : bvmap 5 word) mem' pc fs ys,
  vs_slots (rdW W mem') (spZ regs' + 64) regs ->
  2 ^ 46 <= spZ regs' <= 2 ^ 47 - 64 -> spZ regs' mod 16 = 0 ->
  getr regs' 22 = w64 SB ->
  atoms_ok (Eimg (Ereg regs' (vs_xs regs ++ ys))) fs ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs' (vs_xs regs ++ ys))) (vs_ssK pc fs)
    (restrict (w_H W) (mkst regs' (Z_to_bv 64 (BASE + pc)) mem' (seg_rom SEGS))).
Proof.
intros W regs regs' mem' pc fs ys HSL Hsp Hal H22 HF.
set (E := Eimg (Ereg regs' (vs_xs regs ++ ys))).
assert (E2 : bv_unsigned (ew E 2) = spZ regs') by (subst E; rewrite (vs_EE regs' _ 2 2%bv eq_refl); reflexivity).
assert (E22 : ew E 22 = Z_to_bv 64 SB) by (subst E; rewrite (vs_EE regs' _ 22 22%bv eq_refl); exact H22).
assert (CH : forall i r off, nth_error vs_saved i = Some r -> off = 56 - 8 * Z.of_nat i ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem') (spZ regs') (YP09.mkChunk off (CVal 8 (SOff (32 + i) 0)))).
{ intros i r off Hr Ho. pose proof (HSL i r Hr) as Hw.
  apply (chunk_ok_val SEGS E _ (spZ regs') off 8 (SOff (32 + i) 0) (bv_unsigned (getr regs r)));
    [cbn [sv_denot]; subst E; rewrite (vs_Ex regs' regs ys i r Hr), Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
    | pose proof (bv_unsigned_in_range 64 (getr regs r)) as R; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in R; exact R
    | zside |].
  replace (spZ regs' + off) with (spZ regs' + 64 - 8 - 8 * Z.of_nat i) by lia.
  exact (val_mem_of_rdword SEGS _ _ _ _ Hw). }
rewrite restrict_mkst_fx. unfold vs_ssK. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, vs_slots_r.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil;
  first [ apply (CH 7%nat 22%bv); reflexivity | apply (CH 6%nat 21%bv); reflexivity | apply (CH 5%nat 20%bv); reflexivity
        | apply (CH 4%nat 19%bv); reflexivity | apply (CH 3%nat 18%bv); reflexivity | apply (CH 2%nat 9%bv); reflexivity
        | apply (CH 1%nat 8%bv); reflexivity | apply (CH 0%nat 1%bv); reflexivity ].
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. split.
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2. change (2 ^ 4) with 16. lia.
  + split; [|exact HF]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E22, unsigned_lit_small by (unfold SB; lia).
    rewrite Z.pow_0_r, Z.mod_1_r. unfold SB. lia.
Qed.

Section e.
Variable B : asyms.
Variables gotw guard : Z.

(* the entry of a walk *)
Record vsE := mkVsE {
  e_ly : alayout; e_S : astate; e_W : world SEGS; e_regs : bvmap 5 word; e_mem : word -> option byte;
  e_md : Model; e_ch : list (Z * Z * Z); e_seg : Z; e_parent : Z; e_vid : Z; e_s : list Z }.
Definition e_sp (e : vsE) : Z := spZ (e_regs e).
Definition e_FP (e : vsE) : list (Z * Z) := split_W (e_parent e) (e_vid e) (e_s e).
Definition vs_entry (e : vsE) : Prop :=
  afn_pre SEGS B STK_reac_declared_vlan_split (e_ly e) (e_S e) (e_W e) (e_regs e) (e_mem e) (e_md e) (e_ch e) /\
  arodata_okP SEGS SEG_RLO SEG_RHI B (rdW (e_W e) (e_mem e)) /\
  getr (e_regs e) 10 = w64 (e_seg e) /\ 0 <= e_seg e < 2 ^ 64 /\
  getr (e_regs e) 11 = w64 (e_parent e) /\ 0 <= e_parent e < 2 ^ 64 /\
  getr (e_regs e) 12 = w64 16 /\
  getr (e_regs e) 13 = w64 (e_vid e) /\ 0 <= e_vid e < 2 ^ 64 /\
  split_pre SEGS B (e_ly e) (e_S e) (e_W e) (e_mem e) (e_regs e) (e_seg e) (e_parent e) 16 (e_vid e) (e_s e)
    gotw guard /\
  st_nev (e_S e) <= EV_MAX.
(* the functional post and the goal of every segment *)
Definition vs_Q (e : vsE) : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' W' regs' mem' md' =>
  getr regs' 10 = w64 (match SegModel.vlan_split (e_s e) with Some _ => 1 | None => 0 end) /\
  (match SegModel.vlan_split (e_s e) with
   | Some (p, v) => sa_strz (rdW W' mem') (e_parent e) p /\ sa_val (rdW W' mem') (e_vid e) 2 v
   | None => True
   end) /\
  sa_kept SEGS (e_W e) (e_mem e) W' mem' (e_regs e) STK_reac_declared_vlan_split (split_E (e_parent e) (e_vid e) (e_s e)) /\
  sa_noalloc B (e_ly e) (e_S e) ly' S'.
Definition vs_goal (e : vsE) (W' : world SEGS) (c : config) : Prop :=
  SRr SEGS W' c (apost_base SEGS B STK_reac_declared_vlan_split (e_FP e) (e_regs e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
    EV_reac_declared_vlan_split (vs_Q e)).
Definition vs_cfg (pc : Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : config :=
  mkCfg (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)) md.

(* the registers the body keeps from the prologue on: sp below the frame, gp, tp, s0 = vid, s1 = parent,
   s2 = segment, s3 = cap = 16, s6 = SB, s7 .. s11 the entry's *)
Definition vs_regs (e : vsE) (regs' : bvmap 5 word) : Prop :=
  spZ regs' = e_sp e - 64 /\ getr regs' 3 = getr (e_regs e) 3 /\ getr regs' 4 = getr (e_regs e) 4 /\
  getr regs' 8 = w64 (e_vid e) /\ getr regs' 9 = w64 (e_parent e) /\ getr regs' 18 = w64 (e_seg e) /\
  getr regs' 19 = w64 16 /\ getr regs' 22 = w64 SB /\
  (forall r, 23 <= r <= 27 -> getr regs' (Z_to_bv 5 r) = getr (e_regs e) (Z_to_bv 5 r)).
(* a state before the name_ok call: the world, layout and model state of the entry, the journal from the entry,
   the frame, and every byte outside the stack window and the range Wr the body has written as at the entry
   (vs_ctx0: nothing written; the errno cell strtol writes keeps its value: SegBridge.bridge_strtol10_errno) *)
Definition vs_ctxW (e : vsE) (Wr : Z -> Prop) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  ajournal SEGS B STK_reac_declared_vlan_split (e_sp e) (e_FP e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) []
    (e_ly e) (e_S e) (e_W e) mem' md' 0 /\
  vs_regs e regs' /\ vs_slots (rdW (e_W e) mem') (e_sp e) (e_regs e) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (e_sp e - STK_reac_declared_vlan_split <= a < e_sp e) -> ~ Wr a -> rdW (e_W e) mem' a = rdW (e_W e) (e_mem e) a) /\
  (forall a, apresent (w_H (e_W e)) (e_mem e) a -> apresent (w_H (e_W e)) mem' a).
Definition vs_ctx0 (e : vsE) : bvmap 5 word -> (word -> option byte) -> Model -> Prop := vs_ctxW e (fun _ => False).

(* ---- the statements of the points ---- *)
(* KR: the epilogue with a0 = v, from any state the journal reaches whose post holds of a0 = v *)
Definition vs_KR_stmt : Prop :=
  forall e ly' S' W' regs' mem' md' v, vs_entry e ->
  ajournal SEGS B STK_reac_declared_vlan_split (e_sp e) (e_FP e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [] ly' S' W' mem' md' 0 ->
  spZ regs' = e_sp e - 64 -> getr regs' 3 = getr (e_regs e) 3 -> getr regs' 4 = getr (e_regs e) 4 ->
  (forall r, 23 <= r <= 27 -> getr regs' (Z_to_bv 5 r) = getr (e_regs e) (Z_to_bv 5 r)) -> getr regs' 22 = w64 SB ->
  vs_slots (rdW W' mem') (e_sp e) (e_regs e) ->
  getr regs' 10 = w64 v ->
  (forall regs'' md'', getr regs'' 10 = w64 v -> vs_Q e ly' S' W' regs'' mem' md'') ->
  vs_goal e W' (vs_cfg VS_KR regs' mem' md').
(* the tail after the dot at di, the digits strtol reads *)
Definition vs_tail (e : vsE) (di : nat) : list Z := skipn (S di) (e_s e).
(* K1, 0x89bec: a0 = strrchr's answer, the dot's address or 0 *)
Definition vs_K1_stmt : Prop :=
  forall e regs' mem' md' r, vs_entry e -> vs_ctx0 e regs' mem' md' ->
  getr regs' 10 = w64 r ->
  ((r = 0 /\ SegModel.strrchr (e_s e) 46 = None) \/
   (exists di, SegModel.strrchr (e_s e) 46 = Some di /\ r = e_seg e + Z.of_nat di)) ->
  vs_goal e (e_W e) (vs_cfg VS_K1 regs' mem' md').
(* KL, 0x89c24, pass j: a0 = dot + 1, a1 = a2 = dot + 2 + j, a3 = 9, a4 = the (non-NUL) byte dot[1 + j], s4 = dot;
   the j bytes dot[1 .. j] are digits *)
Definition vs_KL_stmt (j : nat) : Prop :=
  forall e regs' mem' md' di, vs_entry e -> vs_ctx0 e regs' mem' md' ->
  SegModel.strrchr (e_s e) 46 = Some di -> di <> 0%nat -> (S di + j < length (e_s e))%nat ->
  forallb SegModel.isdigit (firstn j (vs_tail e di)) = true ->
  getr regs' 10 = w64 (e_seg e + Z.of_nat di + 1) ->
  getr regs' 11 = w64 (e_seg e + Z.of_nat di + 2 + Z.of_nat j) ->
  getr regs' 12 = w64 (e_seg e + Z.of_nat di + 2 + Z.of_nat j) ->
  getr regs' 13 = w64 9 ->
  getr regs' 14 = w64 (nth (S di + j) (e_s e) 0) ->
  getr regs' 20 = w64 (e_seg e + Z.of_nat di) ->
  vs_goal e (e_W e) (vs_cfg VS_KL regs' mem' md').
(* K2, 0x89c60: the tail is a non-empty run of digits; a0 = dot + 1, s4 = dot *)
Definition vs_K2_stmt : Prop :=
  forall e regs' mem' md' di, vs_entry e -> vs_ctx0 e regs' mem' md' ->
  SegModel.strrchr (e_s e) 46 = Some di -> di <> 0%nat -> vs_tail e di <> [] ->
  forallb SegModel.isdigit (vs_tail e di) = true ->
  getr regs' 10 = w64 (e_seg e + Z.of_nat di + 1) ->
  getr regs' 20 = w64 (e_seg e + Z.of_nat di) ->
  vs_goal e (e_W e) (vs_cfg VS_K2 regs' mem' md').
(* K3, 0x89c6c: a0 = strtol's value of the tail *)
Definition vs_K3_stmt : Prop :=
  forall e regs' mem' md' di, vs_entry e -> vs_ctx0 e regs' mem' md' ->
  SegModel.strrchr (e_s e) 46 = Some di -> di <> 0%nat -> vs_tail e di <> [] ->
  forallb SegModel.isdigit (vs_tail e di) = true ->
  getr regs' 10 = w64 (SegModel.strtol10 (vs_tail e di)) ->
  getr regs' 20 = w64 (e_seg e + Z.of_nat di) ->
  vs_goal e (e_W e) (vs_cfg VS_K3 regs' mem' md').
(* K4, 0x89cd0: the value in range; a0 = strlen of the segment, s4 = plen = di, s5 = v *)
Definition vs_K4_stmt : Prop :=
  forall e regs' mem' md' di v, vs_entry e -> vs_ctx0 e regs' mem' md' ->
  SegModel.strrchr (e_s e) 46 = Some di -> di <> 0%nat -> vs_tail e di <> [] ->
  forallb SegModel.isdigit (vs_tail e di) = true -> v = SegModel.strtol10 (vs_tail e di) -> 1 <= v <= 4094 ->
  getr regs' 10 = w64 (Z.of_nat (length (e_s e))) ->
  getr regs' 20 = w64 (Z.of_nat di) -> getr regs' 21 = w64 v ->
  vs_goal e (e_W e) (vs_cfg VS_K4 regs' mem' md').
(* K5, 0x89cec: parent[0 .. di) holds the segment's first di bytes, and only those bytes outside the window moved *)
Definition vs_K5_stmt : Prop :=
  forall e regs' mem' md' di v, vs_entry e ->
  vs_ctxW e (fun a => e_parent e <= a < e_parent e + Z.of_nat di) regs' mem' md' ->
  SegModel.strrchr (e_s e) 46 = Some di -> di <> 0%nat -> vs_tail e di <> [] ->
  forallb SegModel.isdigit (vs_tail e di) = true -> v = SegModel.strtol10 (vs_tail e di) -> 1 <= v <= 4094 ->
  getr regs' 20 = w64 (Z.of_nat di) -> getr regs' 21 = w64 v ->
  (forall i, (i < di)%nat -> rdW (e_W e) mem' (e_parent e + Z.of_nat i) = Some (nth i (e_s e) 0)) ->
  vs_goal e (e_W e) (vs_cfg VS_K5 regs' mem' md').
(* K6, 0x89d0c: after name_ok; a0 = name_ok's answer on the parent string parent holds *)
Definition vs_K6_stmt : Prop :=
  forall e ly' S' W' regs' mem' md' di v, vs_entry e ->
  ajournal SEGS B STK_reac_declared_vlan_split (e_sp e) (e_FP e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [] ly' S' W' mem' md' 0 ->
  vs_regs e regs' -> vs_slots (rdW W' mem') (e_sp e) (e_regs e) ->
  SegModel.strrchr (e_s e) 46 = Some di -> di <> 0%nat -> vs_tail e di <> [] ->
  forallb SegModel.isdigit (vs_tail e di) = true -> v = SegModel.strtol10 (vs_tail e di) -> 1 <= v <= 4094 ->
  getr regs' 21 = w64 v ->
  getr regs' 10 = w64 (seg_spec.b2z (SegModel.name_ok (firstn di (e_s e)))) ->
  sa_strz (rdW W' mem') (e_parent e) (firstn di (e_s e)) ->
  sa_noalloc B (e_ly e) (e_S e) ly' S' ->
  (forall i, 0 <= i < 2 -> apresent (w_H W') mem' (e_vid e + i)) ->
  range_addressable (rdW W' mem') SHADOW_OFF (e_vid e) 2 ->
  sa_kept SEGS (e_W e) (e_mem e) W' mem' (e_regs e) STK_reac_declared_vlan_split (fun a => e_parent e <= a < e_parent e + Z.of_nat di + 1) ->
  vs_goal e W' (vs_cfg VS_K6 regs' mem' md').
End e.
End f.
End d.
