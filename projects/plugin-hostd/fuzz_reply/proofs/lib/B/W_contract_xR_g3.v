(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_LLVMFuzzerTestOneInput_exit_x.v, with its module paths, module names and numbers changed; 153 of its 247 lines of code are new or changed and 8437 lines of the source are left out. *)
(* Contract texts at a world relation R, image B: list_drop (lib/B/W_contract_x.v ldrop_post_x :603, ldrop_spec_x :623)
   and the block lx_ends of SEG_EXIT (lib/B/W_bx_defs_x.v lx_ends_post_x :195, lx_ends_S_x :222).  A beside-file of
   W_contract_xR.v (a Theorem Labs lane's), in its form: R is a Section variable right after ARx, with its laws R_refl, R_trans,
   WLE_R (the definitions use none of them), and the SAME R is in the post journal (W_journal_x.ajournal_gx_xR) and in
   the step relation (YA0nH.SRrG SEGS R).
   Against the strict texts only these change: the name, `ajournal_gx_x SEGS B PST ARx` -> `ajournal_gx_xR SEGS B PST
   ARx R`, `SRr SEGS` -> `SRrG SEGS R`, the post names X_post_x -> X_post_xR.  The comments inside the strict texts are
   left out.
   Instances: at R := wle each R text IS its strict text (X_x_wle, by conversion); the R text at wle gives the strict
   one (X_x_of_xR); a strict text gives the R text at every R that contains wle (X_xR_of_x, from WLE_R), for every text
   whose premises carry no journal (all but lx_ends_S_x).  The satisfiability lemmas at the real image are in
   W_contract_xR_g3_sat.v.
   rule 24: proves no function (kind: statement text; contract twins, no walk). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Setoid.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_kit W_journal W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YI00 YN0h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require next_line_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require send_line_c send_line_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayRunT drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require gesture_end_c relay_remove_b_c relay_instance_gone_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require gesture_end_b_c RelayRunF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YCe5x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require ListTr HarnessTr RelayRunF.
(* the import block above is W_contract_x.v's (lines 43-78), so every name of the texts resolves as there *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
(* the statement side of lib/B/W_bx_defs_x.v (its import block, lines 35-54), for lx_ends_post_x / lx_ends_S_x *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a YN1e YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_place W_tbl W_pl W_img.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_frame_x W_img_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_bx_defs W_bx_defs_x.
(* RelocB's sink-instance guard, after every Import of YE2k: no sink class is a hint after it *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* list_drop: W_contract_x.v Section w1 at R *)
Section w1R.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable G : list (Z * Z).
(* W_contract_x.v:603 ldrop_post_x at R *)
Definition ldrop_post_xR (regs : bvmap 5 word) ly S (Hp : list Z) (W : world SEGS) (mem : word -> option byte) (md : Model)
(LA : Z) (l : HarnessRep.hlist) (lines : bool) (i : nat) (kr : nat) : world SEGS -> config -> Prop :=
fun W' c' => exists ly' S' Hp' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
ajournal_gx_xR SEGS B PST ARx R G 0 [] LDROP_STK (spZ regs)
[(HarnessRep.hl_v l, HarnessRep.hl_v l + AREC * HarnessRep.hl_cap l);
 (fst (nth i (HarnessRep.hl_recs l) (0, [])),
  fst (nth i (HarnessRep.hl_recs l) (0, [])) + req_size (Z.of_nat (length (snd (nth i (HarnessRep.hl_recs l) (0, [])))) + 1))]
ly S Hp W mem md [] ly' S' Hp' W' mem' md' 1 /\
aregs_preserved regs regs' /\
apres_kept B W mem W' mem' /\
(forall j, 0 <= j < 4 -> aview SEGS (w_H W') mem' (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j)) /\
alist_at B ly' S' W' mem' LA (ldrop_list l i) lines /\
(exists b1 b2, ablocks B ly S = b1 ++ (fst (nth i (HarnessRep.hl_recs l) (0, [])),
 Z.of_nat (length (snd (nth i (HarnessRep.hl_recs l) (0, [])))) + 1) :: b2 /\ ablocks B ly' S' = b1 ++ b2) /\
mo_le MT S S' (mo_free MT) /\ rp_RM RP S' kr.
(* W_contract_x.v:623 ldrop_spec_x at R *)
Definition ldrop_spec_xR (pc : Z) : Prop :=
forall W ly S Hp regs mem md ch LA l lines i,
afn_pre_x SEGS B ARx LDROP_STK ly S Hp W regs mem md ch ->
getr regs 10 = w64 LA -> getr regs 11 = w64 (Z.of_nat i) ->
alist_at B ly S W mem LA l lines ->
(i < length (HarnessRep.hl_recs l))%nat ->
LA mod 8 = 0 -> 4096 <= LA ->
AREC * (HarnessRep.hl_n l - 1 - Z.of_nat i) < 2 ^ 32 ->
azs B LA 16 ->
(forall a, LA <= a < LA + 16 -> inG G a /\ ~ (spZ regs - LDROP_STK <= a < spZ regs)) ->
(forall a, HarnessRep.hl_v l <= a < HarnessRep.hl_v l + AREC * HarnessRep.hl_cap l -> ~ (spZ regs - LDROP_STK <= a < spZ regs)) ->
mo_ok MT S (mo_free MT) ->
forall kr : nat,
rp_RM RP S (Z.to_nat (mo_free MT_rk) + kr) ->
cnt_ok_pk RP ldrop_pk (ablocks B ly S) ->
rom_view SEGS W mem ->
SRrG SEGS R W (cfg_at SEGS pc regs mem md) (ldrop_post_xR regs ly S Hp W mem md LA l lines i kr).
End w1R.

(* ---- the instances ---- *)
Section w1Ri.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable G : list (Z * Z).
Lemma ldrop_post_x_wle : ldrop_post_x B PST ARx MT RP G = ldrop_post_xR B PST ARx (@wle SEGS) MT RP G.
Proof. reflexivity. Qed.
Lemma ldrop_spec_x_wle : ldrop_spec_x B PST ARx MT RP G = ldrop_spec_xR B PST ARx (@wle SEGS) MT RP G.
Proof. reflexivity. Qed.
Lemma ldrop_spec_x_of_xR : forall pc, ldrop_spec_xR B PST ARx (@wle SEGS) MT RP G pc -> ldrop_spec_x B PST ARx MT RP G pc.
Proof. intros pc H. exact H. Qed.
Lemma ldrop_post_xR_of_x : forall regs ly S Hp W mem md LA l lines i kr W' c',
  ldrop_post_x B PST ARx MT RP G regs ly S Hp W mem md LA l lines i kr W' c' ->
  ldrop_post_xR B PST ARx R MT RP G regs ly S Hp W mem md LA l lines i kr W' c'.
Proof.
intros regs ly S Hp W mem md LA l lines i kr W' c' (ly' & S' & Hp' & regs' & mem' & md' & Hc & HJ & REST).
exists ly', S', Hp', regs', mem', md'. split; [exact Hc|]. split; [|exact REST].
eapply ajournal_gx_xR_mono; [exact WLE_R | exact HJ].
Qed.
Lemma ldrop_spec_xR_of_x : forall pc, ldrop_spec_x B PST ARx MT RP G pc -> ldrop_spec_xR B PST ARx R MT RP G pc.
Proof.
intros pc H. unfold ldrop_spec_xR. intros.
eapply SRrG_mono; [eapply SRr_SRrG; [exact WLE_R | eapply H; eassumption] |].
intros W' c' _ HP. eapply ldrop_post_xR_of_x. exact HP.
Qed.
End w1Ri.

(* the block lx_ends of image B's SEG_EXIT: W_bx_defs_x.v Section lxx at R (only the Section variables the two texts
   use; R right after ARx) *)
Section lxxR.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
Local Notation LLVMF_STK := YCfn.LLVMF_STK.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable LIBROOM NP : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Variable RP : roomp.
Local Notation lx_ends_cost := (W_bx_defs.lx_ends_cost MT).
(* W_bx_defs_x.v:197 lx_ends_post_x at R *)
Definition lx_ends_post_xR (cx : lfcx) (t fpos : Z) (ly3 : alayout) (S3 : astate) (m : lmod)
    (norder : Z) (ord : Z -> Z) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k' (m' : lmod) (afin : Z),
    c' = cfg_at segs (BASE + AX_done) regs' mem' md' /\
    ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly' S' [] W' mem' md' k' /\
    bx_frame cx (frame_addr ly' 1 fpos) W' mem' /\
    sv8 W' mem' (frame_addr ly' 1 fpos + 120) (flag_addr ly' 1 fpos) /\
    frame_addr ly' 1 fpos = frame_addr ly3 1 fpos /\
    amodel_at B ly' S' W' mem' m' /\
    ainput_at B cx ly' S' W' mem' /\
    rom_view segs W' mem' /\ jt_rom W' mem' /\
    ablocks_sep B fr_FP cx m' ly' S' /\
    (forall rest, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
       Permutation (ablocks B ly' S') (input_blks cx ++ model_blks m' ++ rest)) /\
    getr regs' 2 = w64 (lf_F cx) /\ getr regs' 8 = getr (c_regs cx) 2 /\ getr regs' 9 = w64 (lf_F cx) /\
    getr regs' 3 = w64 (as_gp B) /\ getr regs' 4 = w64 (as_tp B) /\
    val_mem segs (arm W' mem') (lf_F cx + AX_AT) 8 afin /\ 0 <= afin /\
    lx_ends_run (lm_gn m) (lm_O m) norder ord (lm_hs m) 0 = Some afin /\
    lm_k m' = lm_k m /\ lm_G m' = lm_G m /\ lm_es m' = lm_es m /\ lm_c m' = lx_ctl_ev (lm_c m) (ct_ev (lm_c m')) /\
    lm_O m' = lm_O m /\ lm_mx m' = lm_mx m /\ lm_cap m' = lm_cap m /\ lm_out m' = lm_out m /\
    lm_gn m' = lm_gn m /\ lm_nfd m' = lm_nfd m /\
    length (lm_hs m') = 4%nat /\
    (forall j, (j < 4)%nat -> lx_slot_evo (nth j (lm_hs m) None) (nth j (lm_hs m') None)) /\
    frames S' = frames S3 /\ mo_le MT S3 S' (lx_ends_cost (lm_hs m)) /\
        NP S' /\ cnt_ok_pk RP (fun _ => 0%nat) (ablocks B ly' S').
(* W_bx_defs_x.v:224 lx_ends_S_x at R *)
Definition lx_ends_S_xR : Prop :=
  forall cx t fpos (ly3 : alayout) (S3 : astate) (m : lmod)
    (norder : Z) (ord : Z -> Z) regs mem (md : Model) (W : world segs) k,
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k ->
  aframe_at cx (frame_addr ly3 1 fpos) W mem ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem ->
  rom_view segs W mem ->
  jt_rom W mem ->
  ablocks_sep B fr_FP cx m ly3 S3 ->
  mo_ok MT S3 (lx_ends_cost (lm_hs m)) ->
  (forall j, (j < 4)%nat -> lx_ends_slot_ok (nth j (lm_hs m) None)) ->
  lx_ends_run (lm_gn m) (lm_O m) norder ord (lm_hs m) 0 <> None ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 8 = getr (c_regs cx) 2 -> getr regs 9 = w64 (lf_F cx) ->
  getr regs 27 = w64 SB -> getr regs 19 = w64 norder ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  1 <= norder <= 4 ->
  val_mem segs (arm W mem) (lf_F cx + AX_AT) 8 0 ->
  (forall i, 0 <= i < norder ->
     val_mem segs (arm W mem) (lf_F cx + AX_ORDER + 4 * i) 4 (ord i) /\ 0 <= ord i < 2 ^ 31) ->
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
    NP S3 -> cnt_ok_pk RP (fun _ => 0%nat) (ablocks B ly3 S3) ->
  SRrG segs R W (cfg_at segs (BASE + AX_after_rf) regs mem md) (lx_ends_post_xR cx t fpos ly3 S3 m norder ord).
End lxxR.

Section lxxRi.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
Local Notation LLVMF_STK := YCfn.LLVMF_STK.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable LIBROOM NP : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable R : world segs -> world segs -> Prop.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Variable RP : roomp.
Local Notation lx_ends_cost := (W_bx_defs.lx_ends_cost MT).
Lemma lx_ends_post_x_wle : lx_ends_post_x B MT NP G_fr fr_FP PST ARx RP = lx_ends_post_xR B MT NP G_fr fr_FP PST ARx (@wle segs) RP.
Proof. reflexivity. Qed.
Lemma lx_ends_S_x_wle : lx_ends_S_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx RP =
  lx_ends_S_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx (@wle segs) RP.
Proof. reflexivity. Qed.
Lemma lx_ends_S_x_of_xR : lx_ends_S_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx (@wle segs) RP ->
  lx_ends_S_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx RP.
Proof. intros H. exact H. Qed.
Lemma lx_ends_post_xR_of_x : forall cx t fpos ly3 S3 m norder ord W' c',
  lx_ends_post_x B MT NP G_fr fr_FP PST ARx RP cx t fpos ly3 S3 m norder ord W' c' ->
  lx_ends_post_xR B MT NP G_fr fr_FP PST ARx R RP cx t fpos ly3 S3 m norder ord W' c'.
Proof.
intros cx t fpos ly3 S3 m norder ord W' c' (ly' & S' & regs' & mem' & md' & k' & m' & afin & Hc & HJ & REST).
exists ly', S', regs', mem', md', k', m', afin. split; [exact Hc|]. split; [|exact REST].
eapply ajournal_gx_xR_mono; [exact WLE_R | exact HJ].
Qed.
(* lx_ends_S_xR_of_x is not stated: lx_ends_S_xR takes its entry journal over R (a premise), which no strict text
   gives back; the strict-to-R direction holds only for the post (lx_ends_post_xR_of_x). *)
End lxxRi.

