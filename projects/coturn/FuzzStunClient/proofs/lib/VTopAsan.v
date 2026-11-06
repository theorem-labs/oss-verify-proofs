(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool String Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import Hoare.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import FContract.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import FContractAsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VStepSound VStepMemSound VParamsCheck VCert VItab VIncl VDriverMatch VContract VDriver VSound VTop VState2 VStepMem2 VCert2 VContract2 VDriverMatch2 VDriver2 VGamma2 VStepMem2SoundA VSound2 VSoundAll2 VSoundMatch2 VSoundCall2x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ flia2 | Zify.zify; xlia zchecker ].  (* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac liae := Z.to_euclidean_division_equations; lia.
Local Ltac niae := Z.to_euclidean_division_equations; nia.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fp_of_fa (FA : FAParams) : FParams :=
  mkFP (fa_entry FA) (fa_ret FA) (fa_tp FA) (fa_frame FA) (fa_prng FA) (fa_errno FA) 0 0 0 0 (fa_nmax FA).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition canon_store2 (cls : Z * Z) : store :=
  mkStore (pm_of_list [(SP0, (Some FContractAsan.F_SPLO, Some FContractAsan.F_SPHI));
                       (DATA, (Some 16, Some ((2 ^ 63 - 1 - fst cls) / 16 * 16)));
                       (SIZE, (Some (fst cls), Some (snd cls)));
                       (FSB, (Some 0, Some (VA_HI - FS_LEN)))])   (* [comment removed for export] *)
          [lsub (ladd (lsym DATA) (lsym SIZE)) (lconst (2 ^ 63 - 1))]
          (pm_of_list [(SP0, (32, 16)); (DATA, (16, 0)); (FSB, (4096, 0))]).

(* [comment removed for export] *)
Definition root_reg2 (FP : FParams) (usp k : Z) : option lin :=
  if Z.eqb k 2 then Some (lsymc SP0 usp) else root_reg FP k.

Definition root_regs_ok2 (FP : FParams) (usp : Z) (m : pmap lin) : bool :=
  forallb (fun k => match pm_get (reg_key k) m with
                    | None => true
                    | Some e => match root_reg2 FP usp k with
                                | Some e' => lin_eqb e e'
                                | None => false
                                end
                    end) (zseq 1 31).

(* [comment removed for export] *)
Definition root_pre1_ok (FA : FAParams) (cls : Z * Z) (usp : Z) (cs : cstate) : bool :=
  root_regs_ok2 (fp_of_fa FA) usp (vs_regs (load_cstate cs 0 []))
  && is_nilb (cs_slots cs) && is_nilb (cs_globs cs) && is_nilb (cs_nul cs)
  && is_nilb (cs_valset cs) && is_nilb (cs_conddef cs) && is_nilb (cs_moddef cs)
  && store_le (canon_store2 cls) (store_of cs).

(* [comment removed for export] *)
Definition root_shf_ok (fr usp : Z) (s : srgn) : bool :=
  match sr_kind s with
  | SK_shadow o => Pos.eqb o SP0 && Pos.eqb (sr_base s) SP8 && is_nilb (sr_nul s)
                   && match sr_b8 s with None => true | Some _ => false end
                   && forallb (fun c : Z * (Z * lin) => match c with (k, (w, e)) =>
                        Z.leb (- (fr / 8)) k && Z.ltb 0 w && Z.leb (k + w) (usp / 8) && lin_eqb e (lconst 0) end) (sr_cells s)
  | _ => false
  end.

Definition root_pre_ok2 (FA : FAParams) (cls : Z * Z) (usp : Z) (cs : cstate2) : bool :=
  root_pre1_ok FA cls usp (c1 cs)
  && is_nilb (cs_live cs) && is_nilb (cs_divdef cs)
  && match cs_rgn cs with [s] => root_shf_ok (fa_frame FA) usp s | _ => false end.

(* [comment removed for export] *)
Definition root_exit_ok2 (FA : FAParams) (usp : Z) (cs : cstate2) : bool :=
  root_exit_ok (c1 cs)
  && is_nilb (cs_live cs)
  && match cs_rgn cs with
     | [s] => match sr_kind s with
              | SK_shadow o => Pos.eqb o SP0 && Pos.eqb (sr_base s) SP8
                               && existsb (fun c : Z * cell => match c with (k, (w, Some e)) =>
                                    Z.eqb k (- (fa_frame FA / 8)) && Z.eqb w (fa_frame FA / 8 + usp / 8) && lin_eqb e (lconst 0) | _ => false end)
                                          (cm_of_list (sr_cells s))
              | _ => false
              end
     | _ => false
     end.

(* [comment removed for export] *)
Definition root_res (U : vunit2) : Z := 16 + u_sp (u1 U).

Definition root_ok2 (FA : FAParams) (U : vunit2) : bool :=
  let V := u1 U in
  match u_root V with
  | None => false
  | Some r =>
  Z.eqb r (fa_ret FA)
  && Z.eqb (u_entry V) (fa_entry FA)
  && (Z.eqb (u_sp V) 0 || Z.eqb (u_sp V) (-16))
  && is_nilb (u_wstack V)
  && forallb (fun c : Z * Z => Z.eqb (fst c) (fa_prng FA) && Z.eqb (snd c) 8) (u_wglobs V)
  && (is_nilb (u2_wrgn U) && Z.leb 0 (u2_fdepth U))
  && Z.leb (fst (u_sclass V)) (snd (u_sclass V))
  && root_pre_ok2 FA (u_sclass V) (u_sp V) (u2_pre U)
  && forallb (root_exit_ok2 FA (u_sp V)) (u2_exits U)
  end.

Definition roots2 (FA : FAParams) (res : Z) (C : vcert2) : list vunit2 :=
  List.filter (fun U => root_ok2 FA U && Z.eqb (root_res U) res) C.

(* [comment removed for export] *)
Definition roots_ok2 (FA : FAParams) (C : vcert2) : bool :=
  cover (S (length C)) (map (fun U => u_sclass (u1 U)) (roots2 FA 0 C)) 0 (fa_nmax FA)
  && cover (S (length C)) (map (fun U => u_sclass (u1 U)) (roots2 FA 16 C)) 0 (fa_nmax FA).

(* [comment removed for export] *)
Definition roots_resb (FA : FAParams) (res other : Z) (C : vcert2) : bool :=
  cover (S (length C)) (map (fun U => u_sclass (u1 U)) (roots2 FA res C)) 0 (fa_nmax FA)
  && match roots2 FA other C with [] => true | _ => false end.

Lemma cover_mono : forall f f' cls cur hi, (f <= f')%nat -> cover f cls cur hi = true -> cover f' cls cur hi = true.
Proof.
  induction f as [|f IH]; intros f' cls cur hi Hle H; [discriminate|].
  destruct f' as [|f']; [lia|]. cbn [cover] in H |- *.
  destruct (Z.leb hi cur); [reflexivity|].
  destruct (find _ cls) as [c|]; [|discriminate]. apply (IH f'); [lia|exact H].
Qed.

Lemma roots_ok2_of_resb : forall FA C0 C16,
  roots_resb FA 0 16 C0 = true -> roots_resb FA 16 0 C16 = true -> roots_ok2 FA (C0 ++ C16)%list = true.
Proof.
  intros FA C0 C16 H0 H16. unfold roots_resb in H0, H16. unfold roots_ok2, roots2 in *.
  apply andb_prop in H0 as [C0c C0n]. apply andb_prop in H16 as [C16c C16n].
  rewrite !List.filter_app.
  destruct (List.filter _ C0) as [|? ?] eqn:E0 in C0n; [|discriminate].
  destruct (List.filter _ C16) as [|? ?] eqn:E16 in C16n; [|discriminate].
  rewrite E16, E0, app_nil_r. cbn [app]. rewrite length_app.
  apply andb_true_intro. split; [eapply cover_mono; [|exact C0c]; lia | eapply cover_mono; [|exact C16c]; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac bsplit H :=
  repeat match type of H with
         | (_ && _) = true => apply andb_prop in H; destruct H as [H ?]
         end.

Lemma root_ok2_facts FA U :
  root_ok2 FA U = true ->
  u_root (u1 U) = Some (fa_ret FA) /\ u_entry (u1 U) = fa_entry FA /\ (u_sp (u1 U) = 0 \/ u_sp (u1 U) = -16) /\ u_wstack (u1 U) = []
  /\ (forall c, In c (u_wglobs (u1 U)) -> c = (fa_prng FA, 8))
  /\ (u2_wrgn U = [] /\ 0 <= u2_fdepth U)
  /\ fst (u_sclass (u1 U)) <= snd (u_sclass (u1 U))
  /\ root_pre_ok2 FA (u_sclass (u1 U)) (u_sp (u1 U)) (u2_pre U) = true
  /\ (forall X, In X (u2_exits U) -> root_exit_ok2 FA (u_sp (u1 U)) X = true).
Proof.
  unfold root_ok2. intros H.
  destruct (u_root (u1 U)) as [r|]; [|discriminate].
  apply andb_prop in H as [H H9]. apply andb_prop in H as [H H8]. apply andb_prop in H as [H H7]. apply andb_prop in H as [H H6].
  apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. subst r. apply Z.eqb_eq in H2. apply is_nilb_nil in H4.
  assert (H3' : u_sp (u1 U) = 0 \/ u_sp (u1 U) = -16) by (apply orb_prop in H3 as [H3|H3]; apply Z.eqb_eq in H3; [left|right]; exact H3).
  apply andb_prop in H6 as [H6 H6']. apply is_nilb_nil in H6. apply Z.leb_le in H6'.
  apply Z.leb_le in H7. rewrite forallb_forall in H5. rewrite forallb_forall in H9.
  split; [reflexivity|]. split; [exact H2|]. split; [exact H3'|]. split; [exact H4|]. split.
  { intros [a w] Hc. specialize (H5 _ Hc). apply andb_prop in H5 as [Y1 Y2]. simpl in Y1, Y2.
    apply Z.eqb_eq in Y1. apply Z.eqb_eq in Y2. now subst. }
  split; [split; [exact H6|exact H6']|]. split; [exact H7|]. split; [exact H8|]. exact H9.
Qed.

Lemma root_pre_ok2_facts FA cls usp0 cs :
  root_pre_ok2 FA cls usp0 cs = true ->
  root_regs_ok2 (fp_of_fa FA) usp0 (vs_regs (load_cstate (c1 cs) 0 [])) = true
  /\ cs_slots (c1 cs) = [] /\ cs_globs (c1 cs) = [] /\ cs_nul (c1 cs) = []
  /\ cs_valset (c1 cs) = [] /\ cs_conddef (c1 cs) = [] /\ cs_moddef (c1 cs) = []
  /\ store_le (canon_store2 cls) (store_of (c1 cs)) = true
  /\ cs_live cs = [] /\ cs_divdef cs = []
  /\ exists s, cs_rgn cs = [s] /\ root_shf_ok (fa_frame FA) usp0 s = true.
Proof.
  unfold root_pre_ok2, root_pre1_ok. intros H.
  apply andb_prop in H as [H R]. apply andb_prop in H as [H DD]. apply andb_prop in H as [H LV].
  apply andb_prop in H as [H Q8]. apply andb_prop in H as [H Q7]. apply andb_prop in H as [H Q6]. apply andb_prop in H as [H Q5].
  apply andb_prop in H as [H Q4]. apply andb_prop in H as [H Q3]. apply andb_prop in H as [Q1 Q2].
  destruct (cs_rgn cs) as [|s [|]]; try discriminate.
  split; [exact Q1|]. split; [now apply is_nilb_nil|]. split; [now apply is_nilb_nil|]. split; [now apply is_nilb_nil|].
  split; [now apply is_nilb_nil|]. split; [now apply is_nilb_nil|]. split; [now apply is_nilb_nil|]. split; [exact Q8|].
  split; [now apply is_nilb_nil|]. split; [now apply is_nilb_nil|]. exists s. auto.
Qed.

Lemma root_shf_ok_facts fr usp0 s :
  root_shf_ok fr usp0 s = true ->
  sr_kind s = SK_shadow SP0 /\ sr_base s = SP8 /\ sr_nul s = [] /\ sr_b8 s = None
  /\ forall k w e, In (k, (w, e)) (sr_cells s) -> - (fr / 8) <= k /\ 0 < w /\ k + w <= usp0 / 8 /\ e = lconst 0.
Proof.
  unfold root_shf_ok. intros H. destruct (sr_kind s) as [| | |o]; try discriminate.
  apply andb_prop in H as [H C]. apply andb_prop in H as [H B8]. apply andb_prop in H as [H N]. apply andb_prop in H as [O B].
  apply Pos.eqb_eq in O. subst o. apply Pos.eqb_eq in B.
  split; [reflexivity|]. split; [exact B|]. split; [now apply is_nilb_nil|].
  split; [destruct (sr_b8 s); [discriminate|reflexivity]|].
  intros k w e Hin. rewrite forallb_forall in C. specialize (C _ Hin). cbn beta iota in C.
  apply andb_prop in C as [C C4]. apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2].
  apply Z.leb_le in C1. apply Z.ltb_lt in C2. apply Z.leb_le in C3. apply lin_eqb_eq in C4. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fzones_std (fr shoff : Z) : list fzone :=
  [ mkFZ SP8 shoff (lconst (- (fr / 8))) (lconst 0) true
  ; mkFZ SP8 shoff (lconst (- (fr / 8) - 8)) (lconst (- (fr / 8))) false
  ; mkFZ SP8 shoff (lconst 0) (lconst 8) false
  ; mkFZ FSB 0 (lconst 0) (lconst FS_HINTS) true
  ; mkFZ FSB 0 (lconst FContractAsan.FS_FLAGS) (lconst (FContractAsan.FS_FLAGS + FS_FLAGS_LEN)) true
  ; mkFZ FSB 0 (lconst FContractAsan.FS_FRAMES) (lconst (FContractAsan.FS_FRAMES + FS_FRAMES_LEN)) true
  ; mkFZ FS8 shoff (lconst (FContractAsan.FS_FRAMES / 8)) (lconst (FContractAsan.FS_FRAMES / 8 + FS_FRAMES_LEN / 8)) true
  ; mkFZ FS8 shoff (lconst (FContractAsan.FS_FRAMES / 8 - 8)) (lconst (FContractAsan.FS_FRAMES / 8)) false
  ; mkFZ FS8 shoff (lconst (FContractAsan.FS_FRAMES / 8 + FS_FRAMES_LEN / 8)) (lconst (FContractAsan.FS_FRAMES / 8 + FS_FRAMES_LEN / 8 + 8)) false ].

(* [comment removed for export] *)
Definition fa_genv_prop (G : genv2) (FA : FAParams) : Prop :=
  let P0 := ge2_P0 G in let Q := p1 P0 in
  vp_frame Q = fa_frame FA
  /\ ge2_tp G = fa_tp FA /\ vp_tp P0 = fa_tp FA /\ ci_errno (ge2_CI G) = fa_errno FA
  /\ vp_fcells Q = [(fa_prng FA, 8); (fa_errno FA, 4)]
  /\ fa_nmax FA <= vp_nmax Q
  /\ vp_splo Q <= FContractAsan.F_SPLO /\ FContractAsan.F_SPHI <= vp_sphi Q /\ vp_sphi Q < 2 ^ 64
  /\ (forall r, In r (vp_pristine Q) -> exists r', In r' (fa_pristine FA) /\ fst r' <= fst r /\ snd r <= snd r')
  /\ vp_shoff P0 = fa_shoff FA /\ fa_shoff FA = 0x7fff8000
  /\ vp_fs P0 = Some (FS_LEN, 20) /\ vp_datal P0 = 16
  /\ vp_kcells P0 = map (fun c : Z * Z * Z => (fst (fst c), (snd (fst c), snd c))) (fa_kcells FA)
  /\ vp_kruns P0 = map (fun r : Z * Z * Z => (fst (fst r), (fst (fst r) + snd (fst r), snd r))) (fa_gsh FA)
  /\ vp_fzones P0 = fzones_std (fa_frame FA) (fa_shoff FA)
  /\ fa_frame FA mod 64 = 0 /\ 64 <= fa_frame FA /\ fa_frame FA <= 2 ^ 32
  /\ fa_ret FA mod 2 = 0 /\ 0 <= fa_ret FA < 2 ^ 64
  /\ 0 <= fa_tp FA /\ fa_tp FA + 48 <= fa_tsd FA /\ 88 <= fa_tp FA
  /\ 0 <= fa_prng FA /\ fa_prng FA + 8 <= fa_tp FA - 88
  /\ 0 <= fa_errno FA /\ fa_errno FA + 4 <= fa_tp FA - 88
  /\ (forall c, In c (fa_kcells FA) -> 0 <= fst (fst c) /\ 0 < snd (fst c) <= 8 /\ fst (fst c) + snd (fst c) <= 0x7fff7000
                                    /\ 0 <= snd c < 2 ^ (8 * snd (fst c)))
  /\ (forall r, In r (fa_gsh FA) -> fa_shoff FA <= fst (fst r) /\ 0 <= snd (fst r) /\ fst (fst r) + snd (fst r) <= 2 ^ 40 /\ 0 <= snd r < 256)
  /\ (forall r, In r (fa_pristine FA) -> 0 <= fst r /\ snd r <= 0x7fff7000)
  /\ In (fa_tp FA - 88, 8, fa_tsd FA) (fa_kcells FA)
  /\ 0 <= fa_tsd FA /\ fa_tsd FA + 8 <= 0x7fff7000
  (* [comment removed for export] *)
  /\ vp_imgend P0 = fa_imgend FA /\ 0 <= fa_imgend FA /\ fa_tsd FA + 8 <= fa_imgend FA
  /\ (forall r, In r (fa_pristine FA) -> snd r <= fa_imgend FA)
  /\ (forall c, In c (fa_kcells FA) -> fst (fst c) + snd (fst c) <= fa_imgend FA)
  /\ (forall r, In r (fa_gsh FA) -> fst (fst r) + snd (fst r) <= fa_shoff FA + fa_imgend FA / 8)
  /\ fa_imgend FA <= 0x7fff7000.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition root_args (regs : bvmap 5 word) : list Z :=
  map (fun i => bv_unsigned (getr regs (Z_to_bv 5 (10 + Z.of_nat i)))) (seq 0 8).

Definition rootE2 (FA : FAParams) (regs : bvmap 5 word) (sp data : word) (n fs : Z) : venv2 :=
  mkEnv2 (rootE (fp_of_fa FA) regs sp data n) fs (root_args regs) [].

(* [comment removed for export] *)
Definition rootnu2 (E : venv2) : val := nuE E.

Lemma rootnu2_fix E : gamma_fix2 E (rootnu2 E).
Proof. intros s z H. unfold rootnu2, nuE. now rewrite H. Qed.

(* [comment removed for export] *)
Section RootNu.
  Variables (FA : FAParams) (regs : bvmap 5 word) (sp data : word) (n fs : Z).
  Let E2 := rootE2 FA regs sp data n fs.
  #[using="Type"] Lemma rootnu2_SP0 : rootnu2 E2 SP0 = bv_unsigned sp.      Proof. reflexivity. Qed.
  #[using="Type"] Lemma rootnu2_DATA : rootnu2 E2 DATA = bv_unsigned data.  Proof. reflexivity. Qed.
  #[using="Type"] Lemma rootnu2_SIZE : rootnu2 E2 SIZE = n.                 Proof. reflexivity. Qed.
  #[using="Type"] Lemma rootnu2_GP : rootnu2 E2 GP = bv_unsigned (getr regs (Z_to_bv 5 3)). Proof. reflexivity. Qed.
  #[using="Type"] Lemma rootnu2_FSB : rootnu2 E2 FSB = fs.                  Proof. reflexivity. Qed.
  #[using="Type"] Lemma rootnu2_SP8 : rootnu2 E2 SP8 = bv_unsigned sp / 8.  Proof. reflexivity. Qed.
  #[using="Type"] Lemma rootnu2_DATA8 : rootnu2 E2 DATA8 = bv_unsigned data / 8. Proof. reflexivity. Qed.
  #[using="Type"] Lemma rootnu2_FS8 : rootnu2 E2 FS8 = fs / 8.              Proof. reflexivity. Qed.
  #[using="Type"] Lemma rootnu2_SREG r i : In (r, i) sreg_idx -> rootnu2 E2 (SREG i) = bv_unsigned (getr regs (Z_to_bv 5 r)).
  Proof.
    unfold sreg_idx. intros H. simpl in H.
    repeat (destruct H as [H|H]; [inversion H; subst; reflexivity|]). destruct H.
  Qed.
End RootNu.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section PRE.
  Variable SEGS : list Segment.
  Variable FA : FAParams.
  Local Notation readable := (FContractAsan.readable SEGS).
  Local Notation writable := (FContractAsan.writable SEGS).
  Local Notation zeroes := (FContractAsan.zeroes SEGS).
  Local Notation filled := (FContractAsan.filled SEGS).
  Local Notation cell := (FContractAsan.cell SEGS).
  Local Notation shadow := (FContractAsan.shadow FA).
  Local Notation pristine := (FContractAsan.pristine).

  Definition FA_PRE (regs : bvmap 5 word) (mem : word -> option byte) (sp data : word) (n fs ctx thr db : Z) : Prop :=
    let usp := bv_unsigned sp in let ud := bv_unsigned data in
    getr regs 1%bv = Z_to_bv 64 (fa_ret FA) /\ getr regs 2%bv = sp /\ getr regs 4%bv = Z_to_bv 64 (fa_tp FA)
    /\ getr regs 10%bv = data /\ getr regs 11%bv = Z_to_bv 64 n
    /\ 0 <= n < fa_nmax FA /\ ud <> 0 /\ ud + n < 2 ^ 63 /\ ud mod 16 = 0
    /\ (0 < n -> (ud + n <= LOWMEM_TOP \/ HIGHMEM_LO <= ud) /\ ud + n <= VA_HI - 64)
    /\ usp mod 16 = 0 /\ FContractAsan.F_SPLO <= usp /\ usp + 16 <= FContractAsan.F_SPHI
    /\ fs mod 4096 = 0 /\ (fs + FS_LEN <= LOWMEM_TOP \/ HIGHMEM_LO <= fs) /\ fs + FS_LEN <= VA_HI /\ fa_imgend FA <= fs
    /\ (ud + n + 4096 <= usp - fa_frame FA \/ usp + 4112 <= ud)
    /\ (fs + FS_LEN + 4096 <= usp - fa_frame FA \/ usp + 4112 <= fs)
    /\ (fs + FS_LEN + 4096 <= ud \/ ud + n <= fs)
    /\ readable mem ud n
    /\ (0 < n -> forall g, 0 <= 8 * g < n ->
           rdn SEGS mem (Z_to_bv 64 (shadow ud + g)) 1 = Some [Z_to_bv 8 (if 8 * g + 8 <=? n then 0 else n - 8 * g)])
    /\ (0 < n -> readable mem (shadow ud - 2) (n / 8 + 6))
    /\ (0 < n -> readable mem (rd8 (shadow ud)) (rd8 (shadow (ud + n - 1)) + 8 - rd8 (shadow ud)))
    /\ writable mem (usp - fa_frame FA) (fa_frame FA + 16) /\ readable mem usp 16
    /\ zeroes mem (shadow (usp - fa_frame FA)) (fa_frame FA / 8)
    /\ writable mem (shadow (usp - fa_frame FA)) (fa_frame FA / 8 + 2)
    /\ readable mem (shadow (usp - fa_frame FA) - 8) 8 /\ readable mem (shadow usp) 10
    /\ readable mem fs FS_HINTS /\ writable mem fs FS_HINTS
    /\ cell mem (fs + FContractAsan.FS_SSL) 8 20 /\ cell mem (fs + FS_NEEDSGC) 1 0
    /\ zeroes mem (fs + FContractAsan.FS_FLAGS) FS_FLAGS_LEN /\ writable mem (fs + FContractAsan.FS_FLAGS) FS_FLAGS_LEN
    /\ readable mem (fs + FContractAsan.FS_FRAMES) FS_FRAMES_LEN /\ writable mem (fs + FContractAsan.FS_FRAMES) FS_FRAMES_LEN
    /\ readable mem (shadow (fs + FContractAsan.FS_FRAMES) - 8) (FS_FRAMES_LEN / 8 + 16)
    /\ writable mem (shadow (fs + FContractAsan.FS_FRAMES)) (FS_FRAMES_LEN / 8)
    /\ cell mem (fa_tp FA) 8 fs /\ cell mem (fa_tp FA + 0x8) 8 db /\ cell mem (db + 0x18) 8 (fa_tp FA)
    /\ cell mem (fa_tsd FA) 8 ctx /\ cell mem (ctx + 0x98) 8 thr /\ readable mem (thr + 0x30) 16
    /\ ctx <> 0 /\ thr <> 0 /\ 0 < db /\ db + 32 <= 2^64 /\ 0 <= ctx /\ ctx + 160 <= 2^64 /\ 0 <= thr /\ thr + 64 <= 2^64
    /\ apart_writes FA usp fs (db + 0x18) 8 /\ apart_writes FA usp fs (ctx + 0x98) 8 /\ apart_writes FA usp fs (thr + 0x30) 16
    /\ Forall (fun c => cell mem (fst (fst c)) (snd (fst c)) (snd c)) (fa_kcells FA)
    /\ Forall (fun r => filled mem (fst (fst r)) (snd (fst r)) (snd r)) (fa_gsh FA)
    /\ Forall (fun r => pristine mem (fst r) (snd r)) (fa_pristine FA)
    /\ readable mem (fa_prng FA) 8 /\ writable mem (fa_prng FA) 8
    /\ readable mem (fa_errno FA) 4 /\ writable mem (fa_errno FA) 4.

  (* [comment removed for export] *)
  Definition FA_PREA (regs : bvmap 5 word) (mem : word -> option byte) (sp data : word) (a d n fs ctx thr db : Z) : Prop :=
    let usp := a in let ud := bv_unsigned data in
    getr regs 1%bv = Z_to_bv 64 (fa_ret FA) /\ getr regs 2%bv = sp /\ getr regs 4%bv = Z_to_bv 64 (fa_tp FA)
    /\ getr regs 10%bv = data /\ getr regs 11%bv = Z_to_bv 64 n
    /\ 0 <= n < fa_nmax FA /\ ud <> 0 /\ ud + n < 2 ^ 63 /\ ud mod 16 = 0
    /\ (0 < n -> (ud + n <= LOWMEM_TOP \/ HIGHMEM_LO <= ud) /\ ud + n <= VA_HI - 64)
    /\ usp mod 16 = 0 /\ FContractAsan.F_SPLO <= usp /\ usp + 16 <= FContractAsan.F_SPHI
    /\ fs mod 4096 = 0 /\ (fs + FS_LEN <= LOWMEM_TOP \/ HIGHMEM_LO <= fs) /\ fs + FS_LEN <= VA_HI /\ fa_imgend FA <= fs
    /\ (ud + n + 4096 <= usp - fa_frame FA \/ usp + 4096 <= ud)
    /\ (fs + FS_LEN + 4096 <= usp - fa_frame FA \/ usp + 4096 <= fs)
    /\ (fs + FS_LEN + 4096 <= ud \/ ud + n <= fs)
    /\ readable mem ud n
    /\ (0 < n -> forall g, 0 <= 8 * g < n ->
           rdn SEGS mem (Z_to_bv 64 (shadow ud + g)) 1 = Some [Z_to_bv 8 (if 8 * g + 8 <=? n then 0 else n - 8 * g)])
    /\ (0 < n -> readable mem (shadow ud - 2) (n / 8 + 6))
    /\ (0 < n -> readable mem (rd8 (shadow ud)) (rd8 (shadow (ud + n - 1)) + 8 - rd8 (shadow ud)))
    /\ writable mem (usp - fa_frame FA) (fa_frame FA)
    /\ zeroes mem (shadow (usp - fa_frame FA)) (fa_frame FA / 8 - d / 8)
    /\ writable mem (shadow (usp - fa_frame FA)) (fa_frame FA / 8)
    /\ readable mem (shadow (usp - fa_frame FA) - 8) 8 /\ readable mem (shadow usp) 8
    /\ readable mem (shadow (usp - fa_frame FA)) (fa_frame FA / 8)
    /\ readable mem fs FS_HINTS /\ writable mem fs FS_HINTS
    /\ cell mem (fs + FContractAsan.FS_SSL) 8 20 /\ cell mem (fs + FS_NEEDSGC) 1 0
    /\ zeroes mem (fs + FContractAsan.FS_FLAGS) FS_FLAGS_LEN /\ writable mem (fs + FContractAsan.FS_FLAGS) FS_FLAGS_LEN
    /\ readable mem (fs + FContractAsan.FS_FRAMES) FS_FRAMES_LEN /\ writable mem (fs + FContractAsan.FS_FRAMES) FS_FRAMES_LEN
    /\ readable mem (shadow (fs + FContractAsan.FS_FRAMES) - 8) (FS_FRAMES_LEN / 8 + 16)
    /\ writable mem (shadow (fs + FContractAsan.FS_FRAMES)) (FS_FRAMES_LEN / 8)
    /\ cell mem (fa_tp FA) 8 fs /\ cell mem (fa_tp FA + 0x8) 8 db /\ cell mem (db + 0x18) 8 (fa_tp FA)
    /\ cell mem (fa_tsd FA) 8 ctx /\ cell mem (ctx + 0x98) 8 thr /\ readable mem (thr + 0x30) 16
    /\ ctx <> 0 /\ thr <> 0 /\ 0 < db /\ db + 32 <= 2^64 /\ 0 <= ctx /\ ctx + 160 <= 2^64 /\ 0 <= thr /\ thr + 64 <= 2^64
    /\ apart_writes FA (bv_unsigned sp) fs (db + 0x18) 8 /\ apart_writes FA (bv_unsigned sp) fs (ctx + 0x98) 8
    /\ apart_writes FA (bv_unsigned sp) fs (thr + 0x30) 16
    /\ Forall (fun c => cell mem (fst (fst c)) (snd (fst c)) (snd c)) (fa_kcells FA)
    /\ Forall (fun r => filled mem (fst (fst r)) (snd (fst r)) (snd r)) (fa_gsh FA)
    /\ Forall (fun r => pristine mem (fst r) (snd r)) (fa_pristine FA)
    /\ readable mem (fa_prng FA) 8 /\ writable mem (fa_prng FA) 8
    /\ readable mem (fa_errno FA) 4 /\ writable mem (fa_errno FA) 4.

  #[using="Type"] Lemma FA_PRE_anchor regs mem sp data n fs ctx thr db d :
    FA_PRE regs mem sp data n fs ctx thr db -> (d = 0 \/ d = 16) -> bv_unsigned sp mod 32 = 16 - d ->
    fa_frame FA mod 64 = 0 -> 64 <= fa_frame FA ->
    FA_PREA regs mem sp data (bv_unsigned sp + d) d n fs ctx thr db.
  Proof.
    unfold FA_PRE, FA_PREA. cbv zeta. intros PRE Hd Hres F64 F64'.
    destruct PRE as (H1 & H2 & H4 & H10 & H11 & Hn & Hd0 & Hdn & Hd16 & Hdhi & Hsp16 & Hsplo & Hsphi & Hfs4 & Hfslo & Hfshi & Hfsimg
                     & Hdj1 & Hdj2 & Hdj3 & Rd & Rsh & Rshm & Rshw & Wfr & Ru16 & Zsh & Wsh & Rm1 & Rm2 & REST).
    set (usp := bv_unsigned sp) in *.
    pose proof (u_word_lt sp) as Usp. fold usp in Usp.
    unfold FContractAsan.shadow in *. unfold FContractAsan.F_SPLO, FContractAsan.F_SPHI in *.
    unfold FContractAsan.writable, FContractAsan.zeroes, FContractAsan.readable in Wfr, Zsh, Wsh, Rm1, Rm2.
    assert (SF : forall x, x mod 16 = 0 -> (x - fa_frame FA) / 8 = x / 8 - fa_frame FA / 8).
    { intros x Hx. apply Z.mod_divide in F64 as [q Hq]; [|clear; lia]. rewrite Hq. replace (x - q * 64) with (x + (- (q * 8)) * 8) by (clear; lia).
      rewrite Z.div_add by (clear; lia). replace (q * 64) with ((q * 8) * 8) by (clear; lia). rewrite Z.div_mul by (clear; lia). clear; lia. }
    assert (A8 : (usp + d) / 8 = usp / 8 + d / 8).
    { destruct Hd as [-> | ->]; [change (0 / 8) with 0; rewrite !Z.add_0_r; reflexivity|]. replace (usp + 16) with (usp + 2 * 8) by (clear; lia). rewrite Z.div_add by (clear; lia). reflexivity. }
    assert (HI : d = 16 -> usp + 32 <= 0x800000000000).
    { intros ->. pose proof (Z.div_mod usp 32 ltac:(clear; lia)) as D. rewrite Hres in D. clear - D Hsphi. lia. }
    assert (FR8 : 8 <= fa_frame FA / 8) by (apply Z.div_le_lower_bound; clear - F64'; lia).
    rewrite SF in Zsh, Wsh, Rm1 by exact Hsp16. rewrite SF by (destruct Hd as [-> | ->]; [rewrite Z.add_0_r; exact Hsp16|]; pose proof (Z.div_mod usp 16 ltac:(clear; lia)) as D; rewrite Hsp16 in D; replace (usp + 16) with (usp + 1 * 16) by (clear; lia); rewrite Z_mod_plus_full; exact Hsp16).
    rewrite A8.
    repeat (split; [assumption|]).
    split. { destruct Hd as [-> | ->]; [rewrite Z.add_0_r; exact Hsp16|]. replace (usp + 16) with (usp + 1 * 16) by (clear; lia). rewrite Z_mod_plus_full. exact Hsp16. }
    split. { clear - Hsplo Hd. lia. }
    split. { destruct Hd as [-> | ->]; [clear - Hsphi; lia|]. specialize (HI eq_refl). clear - HI; lia. }
    repeat (split; [assumption|]).
    split. { destruct Hdj1 as [X|X]; [left|right]; clear - X Hd; lia. }
    split. { destruct Hdj2 as [X|X]; [left|right]; clear - X Hd; lia. }
    repeat (split; [assumption|]).
    split. { intros i Hi. replace (usp + d - fa_frame FA + i) with (usp - fa_frame FA + (d + i)) by (clear; lia). apply Wfr. clear - Hi Hd. lia. }
    split. { intros i Hi. replace (fa_shoff FA + (usp / 8 + d / 8 - fa_frame FA / 8) + i) with (fa_shoff FA + (usp / 8 - fa_frame FA / 8) + (d / 8 + i)) by (clear; lia).
             apply Zsh. destruct Hd as [-> | ->]; cbn; clear - Hi; lia. }
    split. { intros i Hi. replace (fa_shoff FA + (usp / 8 + d / 8 - fa_frame FA / 8) + i) with (fa_shoff FA + (usp / 8 - fa_frame FA / 8) + (d / 8 + i)) by (clear; lia).
             apply Wsh. destruct Hd as [-> | ->]; cbn; clear - Hi; liae. }
    split. { intros i Hi. destruct (Z.lt_ge_cases (d / 8 + i) 8) as [X|X].
             - replace (fa_shoff FA + (usp / 8 + d / 8 - fa_frame FA / 8) - 8 + i) with (fa_shoff FA + (usp / 8 - fa_frame FA / 8) - 8 + (d / 8 + i)) by (clear; lia).
               apply Rm1. destruct Hd as [-> | ->]; cbn in *; clear - Hi X; lia.
             - replace (fa_shoff FA + (usp / 8 + d / 8 - fa_frame FA / 8) - 8 + i) with (fa_shoff FA + (usp / 8 - fa_frame FA / 8) + (d / 8 + i - 8)) by (clear; lia).
               exists (Z_to_bv 8 0). apply Zsh. destruct Hd as [-> | ->]; cbn in *; clear - Hi X FR8; liae. }
    split. { intros i Hi. replace (fa_shoff FA + (usp / 8 + d / 8) + i) with (fa_shoff FA + usp / 8 + (d / 8 + i)) by (clear; lia).
             apply Rm2. destruct Hd as [-> | ->]; cbn; clear - Hi; liae. }
    split. { intros i Hi. destruct (Z.lt_ge_cases (d / 8 + i) (fa_frame FA / 8)) as [X|X].
             - replace (fa_shoff FA + (usp / 8 + d / 8 - fa_frame FA / 8) + i) with (fa_shoff FA + (usp / 8 - fa_frame FA / 8) + (d / 8 + i)) by (clear; lia).
               exists (Z_to_bv 8 0). apply Zsh. destruct Hd as [-> | ->]; cbn in *; clear - Hi X; lia.
             - replace (fa_shoff FA + (usp / 8 + d / 8 - fa_frame FA / 8) + i) with (fa_shoff FA + usp / 8 + (d / 8 + i - fa_frame FA / 8)) by (clear; lia).
               apply Rm2. destruct Hd as [-> | ->]; cbn in *; clear - Hi X; liae. }
    exact REST.
  Qed.
End PRE.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section ByteFacts.
  Variable SEGS : list Segment.
  (* [comment removed for export] *)
  #[using="Type"] Lemma wordZ_to_bv a : wordZ a = Z_to_bv 64 a. Proof. reflexivity. Qed.

  #[using="Type"] Lemma u_Z_to_bv8 c : 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
  Proof. intros H. rewrite Z_to_bv_unsigned, bv_wrap8_mod. apply Z.mod_small. exact H. Qed.

  #[using="Type"] Lemma readable_at mem0 a n0 x :
    FContractAsan.readable SEGS mem0 a n0 -> a <= x < a + n0 -> exists b, rdn SEGS mem0 (wordZ x) 1 = Some [b].
  Proof. intros H Hx. destruct (H (x - a) ltac:(lia)) as [b Hb]. exists b. rewrite wordZ_to_bv. replace x with (a + (x - a)) by lia. exact Hb. Qed.

  #[using="Type"] Lemma writable_at mem0 a n0 x :
    FContractAsan.writable SEGS mem0 a n0 -> a <= x < a + n0 -> store_ok SEGS mem0 (wordZ x) 1 = true.
  Proof. intros H Hx. rewrite wordZ_to_bv. replace x with (a + (x - a)) by lia. apply H. lia. Qed.

  #[using="Type"] Lemma zeroes_at mem0 a n0 x :
    FContractAsan.zeroes SEGS mem0 a n0 -> a <= x < a + n0 -> exists b, rdn SEGS mem0 (wordZ x) 1 = Some [b] /\ bv_unsigned b = 0.
  Proof.
    intros H Hx. exists (Z_to_bv 8 0). rewrite wordZ_to_bv. replace x with (a + (x - a)) by lia. split; [apply H; lia|]. apply u_Z_to_bv8. lia.
  Qed.

  #[using="Type"] Lemma filled_at mem0 a n0 c x :
    FContractAsan.filled SEGS mem0 a n0 c -> 0 <= c < 256 -> a <= x < a + n0 ->
    exists b, rdn SEGS mem0 (wordZ x) 1 = Some [b] /\ bv_unsigned b = Z.land c 255.
  Proof.
    intros H Hc Hx. exists (Z_to_bv 8 c). rewrite wordZ_to_bv. replace x with (a + (x - a)) by lia. split; [apply H; lia|].
    rewrite u_Z_to_bv8 by exact Hc. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. symmetry. apply Z.mod_small. lia.
  Qed.

  #[using="Type"] Lemma cell_at mem0 a w v :
    FContractAsan.cell SEGS mem0 a w v -> 0 < w <= 8 -> 0 <= v < 2 ^ (8 * w) ->
    exists bs, rdn SEGS mem0 (wordZ a) (Z.to_nat w) = Some bs /\ bytes_le_to_Z bs = v.
  Proof.
    intros H Hw Hv. exists (word_to_le_bytes (Z.to_nat w) (Z_to_bv 64 v)). split; [rewrite wordZ_to_bv; exact H|].
    rewrite bytes_le_N, Z2Nat.id by lia. rewrite u_Z_to_bv64.
    assert (v < 2 ^ 64) by (pose proof (Z.pow_le_mono_r 2 (8 * w) 64 ltac:(lia) ltac:(lia)); lia).
    unfold zwrap. rewrite (Z.mod_small v (2 ^ 64)) by lia. apply Z.mod_small. lia.
  Qed.


End ByteFacts.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section TopA.
  Variable SEGS : list Segment.
  Variable G : genv2.
  Variable FA : FAParams.
  Hypothesis GOK : fa_genv_prop G FA.
  Hypothesis PO0 : params_ok2 SEGS (ge2_P0 G).
  Hypothesis WR : segs_wr_readable SEGS = true.
  (* [comment removed for export] *)
  Hypothesis SEGHI : forall a : word, fa_imgend FA <= bv_unsigned a -> seg_rom SEGS a = None.   (* [comment removed for export] *)

  Variable U : vunit2.
  Hypothesis RU : root_ok2 FA U = true.
  Let P := unit_params2 G U.
  Hypothesis STATIC : unit_static_ok2 G P U = None.
  Let cls := u_sclass (u1 U).
  Let res := root_res U.
  Let FP := fp_of_fa FA.

  (* [comment removed for export] *)
  #[using="GOK RU"] Lemma P_facts :
    vp_frame (p1 P) = fa_frame FA /\ vp_wstack (p1 P) = [(- fa_frame FA, u_sp (u1 U))]
    /\ (forall c, In c (vp_wcells (p1 P)) -> In c (vp_fcells (p1 P)))
    /\ vp_fcells (p1 P) = [(fa_prng FA, 8); (fa_errno FA, 4)]
    /\ vp_shoff P = fa_shoff FA /\ vp_fs P = Some (FS_LEN, 20) /\ vp_datal P = 16 /\ vp_wrgn P = [] /\ vp_tp P = fa_tp FA
    /\ vp_fzones P = fzones_std (fa_frame FA) (fa_shoff FA)
    /\ vp_splo (p1 P) = vp_splo (p1 (ge2_P0 G)) /\ vp_sphi (p1 P) = vp_sphi (p1 (ge2_P0 G)) /\ vp_nmax (p1 P) = vp_nmax (p1 (ge2_P0 G))
    /\ vp_pristine (p1 P) = vp_pristine (p1 (ge2_P0 G)) /\ vp_kcells P = vp_kcells (ge2_P0 G) /\ vp_kruns P = vp_kruns (ge2_P0 G)
    /\ 0 <= vp_fdepth P.
  Proof.
    pose proof GOK as (Gfr & Gtp & Gtp' & Gerr & Gfc & Gnmax & Gsplo & Gsphi & Gsphi' & Gpris & Gsh & Gsh' & Gfs & Gdl & Gkc & Gkr & Gfz
                        & F64 & F64' & F32 & Gret2 & Gret & Gtp0 & Gtp1 & Gtp2 & Gpr0 & Gpr1 & Ger0 & Ger1 & Gkcs & Ggsh & Gprs & Gtsd & Gtsd0 & Gtsd1 & Gimg & Gimg0 & Gimg1 & Gimg2 & Gimg3 & Gimg4 & Gimg5).
    destruct (root_ok2_facts _ _ RU) as (Rroot & Rentry & Rsp & Rws & Rwg & [Rwr Rfd] & _).
    unfold P, unit_params2. cbn. rewrite Rws, Rwr, Gfr. repeat split; try reflexivity; try assumption.
    intros c Hc. unfold unit_wcells2 in Hc. cbn in Hc. rewrite Gfc.
    apply in_app_iff in Hc as [Hc|Hc].
    - destruct (u_errno (u1 U)); [|destruct Hc]. destruct Hc as [<-|[]]. rewrite Gerr. right; left; reflexivity.
    - rewrite (Rwg _ Hc). left; reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="FA RU"] Lemma usp0_cases : u_sp (u1 U) = 0 \/ u_sp (u1 U) = -16.
  Proof. destruct (root_ok2_facts _ _ RU) as (_ & _ & Rsp & _). exact Rsp. Qed.
  #[using="FA RU"] Lemma usp0_div8 : (u_sp (u1 U) = 0 /\ u_sp (u1 U) / 8 = 0 /\ (- u_sp (u1 U)) / 8 = 0)
                    \/ (u_sp (u1 U) = -16 /\ u_sp (u1 U) / 8 = -2 /\ (- u_sp (u1 U)) / 8 = 2).
  Proof. destruct usp0_cases as [E|E]; rewrite E; [left|right]; auto. Qed.

  Section Entry.
    Variables (regs : bvmap 5 word) (mem : word -> option byte) (sp spa data : word) (n fs ctx thr db : Z).
    Hypothesis PRE : FA_PRE SEGS FA regs mem sp data n fs ctx thr db.
    Hypothesis Hcls : fst cls <= n <= snd cls.
    Hypothesis Hres : bv_unsigned sp mod 32 = res.
    (* [comment removed for export] *)
    Hypothesis Hanc : bv_unsigned spa = bv_unsigned sp - u_sp (u1 U).

    Let E2 := rootE2 FA regs spa data n fs.
    Let nu := rootnu2 E2.
    Let S := load_cstate2 P (u2_pre U) (u_entry (u1 U)) [].
    Let usp := bv_unsigned spa.
    Let ud := bv_unsigned data.

    #[using="G GOK RU res PRE Hres Hanc ud"] Lemma A_PRE : FA_PREA SEGS FA regs mem sp data usp (- u_sp (u1 U)) n fs ctx thr db.
    Proof.
      pose proof GOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F64 & F64' & _).
      unfold usp. rewrite Hanc. replace (bv_unsigned sp - u_sp (u1 U)) with (bv_unsigned sp + - u_sp (u1 U)) by lia.
      apply FA_PRE_anchor; [exact PRE| | |exact F64|exact F64'].
      - destruct usp0_cases as [E|E]; rewrite E; [left|right]; reflexivity.
      - rewrite Hres. unfold res, root_res. lia.
    Qed.
    #[using="U res sp data Hres Hanc ud"] Lemma usp_res : usp mod 32 = 16.
    Proof.
      unfold usp. rewrite Hanc. pose proof (Z.div_mod (bv_unsigned sp) 32 ltac:(lia)) as D. rewrite Hres in D. unfold res, root_res in D.
      replace (bv_unsigned sp - u_sp (u1 U)) with (16 + (bv_unsigned sp / 32) * 32) by lia. rewrite Z_mod_plus_full. reflexivity.
    Qed.

    #[using="Type"] Lemma usp_range : 0 <= usp < 2 ^ 64. Proof. apply u_word_lt. Qed.
    #[using="Type"] Lemma ud_range : 0 <= ud < 2 ^ 64. Proof. apply u_word_lt. Qed.
    (* [comment removed for export] *)
    #[using="SEGS G FA GOK U RU res regs mem sp spa data n ctx thr db PRE Hres Hanc usp ud"] Lemma fs_nonneg : 0 <= fs.
    Proof.
      pose proof GOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Gimg0 & _).
      pose proof A_PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfsimg & _). lia.
    Qed.

    (* [comment removed for export] *)
    #[using="GOK RU res sp ud"] Lemma zone_bounds z :
      In z (vp_fzones P) ->
      let lo := zone_lo E2 z in let hi := zone_hi E2 z in
      (   (lo = fa_shoff FA + usp / 8 - fa_frame FA / 8 /\ hi = fa_shoff FA + usp / 8 /\ fz_rw z = true)
       \/ (lo = fa_shoff FA + usp / 8 - fa_frame FA / 8 - 8 /\ hi = fa_shoff FA + usp / 8 - fa_frame FA / 8 /\ fz_rw z = false)
       \/ (lo = fa_shoff FA + usp / 8 /\ hi = fa_shoff FA + usp / 8 + 8 /\ fz_rw z = false)
       \/ (lo = fs /\ hi = fs + FS_HINTS /\ fz_rw z = true)
       \/ (lo = fs + FContractAsan.FS_FLAGS /\ hi = fs + FContractAsan.FS_FLAGS + FS_FLAGS_LEN /\ fz_rw z = true)
       \/ (lo = fs + FContractAsan.FS_FRAMES /\ hi = fs + FContractAsan.FS_FRAMES + FS_FRAMES_LEN /\ fz_rw z = true)
       \/ (lo = fa_shoff FA + fs / 8 + FContractAsan.FS_FRAMES / 8 /\ hi = fa_shoff FA + fs / 8 + FContractAsan.FS_FRAMES / 8 + FS_FRAMES_LEN / 8 /\ fz_rw z = true)
       \/ (lo = fa_shoff FA + fs / 8 + FContractAsan.FS_FRAMES / 8 - 8 /\ hi = fa_shoff FA + fs / 8 + FContractAsan.FS_FRAMES / 8 /\ fz_rw z = false)
       \/ (lo = fa_shoff FA + fs / 8 + FContractAsan.FS_FRAMES / 8 + FS_FRAMES_LEN / 8 /\ hi = fa_shoff FA + fs / 8 + FContractAsan.FS_FRAMES / 8 + FS_FRAMES_LEN / 8 + 8 /\ fz_rw z = false)).
    Proof.
      destruct P_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Gfz & _). rewrite Gfz.
      pose proof GOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F64 & _).
      intros Hz. cbv zeta. unfold fzones_std in Hz. simpl in Hz.
      unfold zone_lo, zone_hi.
      assert (N8 : nuE E2 SP8 = usp / 8) by reflexivity. assert (NF : nuE E2 FSB = fs) by reflexivity. assert (NF8 : nuE E2 FS8 = fs / 8) by reflexivity.
      assert (FR8 : - (fa_frame FA / 8) = (- fa_frame FA) / 8).
      { apply Z.mod_divide in F64 as [q Hq]; [|lia]. rewrite Hq. replace (q * 64) with ((q * 8) * 8) by lia.
        rewrite Z.div_mul by lia. replace (- (q * 8 * 8)) with ((- (q * 8)) * 8) by lia. rewrite Z.div_mul by lia. lia. }
      repeat (destruct Hz as [<-|Hz]; [cbn [fz_disp fz_base fz_lo fz_hi fz_rw]; rewrite ?N8, ?NF, ?NF8, ?eval_lconst; lia|]).
      destruct Hz.
    Qed.
    (* [comment removed for export] *)
    #[using="GOK RU res sp ud"] Lemma rw_zone_cases a :
      in_rw_zones P E2 a = true ->
         (fa_shoff FA + usp / 8 - fa_frame FA / 8 <= a < fa_shoff FA + usp / 8)
      \/ (fs <= a < fs + FS_HINTS)
      \/ (fs + FContractAsan.FS_FLAGS <= a < fs + FContractAsan.FS_FLAGS + FS_FLAGS_LEN)
      \/ (fs + FContractAsan.FS_FRAMES <= a < fs + FContractAsan.FS_FRAMES + FS_FRAMES_LEN)
      \/ (fa_shoff FA + fs / 8 + FContractAsan.FS_FRAMES / 8 <= a < fa_shoff FA + fs / 8 + FContractAsan.FS_FRAMES / 8 + FS_FRAMES_LEN / 8).
    Proof.
      intros Ha. destruct (in_rw_zones_in _ _ _ Ha) as (z & Hz & Hrw & Hin). unfold in_zone in Hin.
      pose proof (zone_bounds z Hz) as ZB. cbv zeta in ZB.
      destruct ZB as [(L & H & _)|[(L & H & R)|[(L & H & R)|[(L & H & _)|[(L & H & _)|[(L & H & _)|[(L & H & _)|[(L & H & R)|(L & H & R)]]]]]]]];
        try (rewrite Hrw in R; discriminate); rewrite L, H in Hin; clear - Hin; lia.
    Qed.

    #[using="SEGS GOK RU res mem sp ctx thr db PRE Hres Hanc usp ud"] Lemma envE : env_ok2 P E2.
    Proof.
      pose proof GOK as (Gfr & Gtp & Gtp' & Gerr & Gfc & Gnmax & Gsplo & Gsphi & Gsphi' & Gpris & Gsh & Gsh' & Gfs & Gdl & Gkc & Gkr & Gfz
                        & F64 & F64' & F32 & Gret2 & Gret & Gtp0 & Gtp1 & Gtp2 & Gpr0 & Gpr1 & Ger0 & Ger1 & Gkcs & Ggsh & Gprs & Gtsd & Gtsd0 & Gtsd1 & Gimg & Gimg0 & Gimg1 & Gimg2 & Gimg3 & Gimg4 & Gimg5).
      pose proof A_PRE as (H1 & H2 & H4 & H10 & H11 & Hn & Hd0 & Hdn & Hd16 & Hdhi & Hsp16 & Hsplo & Hsphi & Hfs4 & Hfslo & Hfshi & Hfsimg
                        & Hdj1 & Hdj2 & Hdj3 & Rd & Rsh & Rshm & Rshw & Wfr & Zsh & Wsh & Rm1 & Rm2 & RZ1 & Rh & Wh & Cssl & Cngc
                        & Zfl & Wfl & Rfr & Wfrm & Rfsh & Wfsh & Ctp & Cdb & Cbeg & Ctsd & Cthr & Rthr
                        & Nctx & Nthr & Db0 & Db1 & Cx0 & Cx1 & Th0 & Th1 & AP1 & AP2 & AP3 & Kc & Kg & Kp & Rpr & Wpr & Rer & Wer).
      destruct P_facts as (Pfr & Pws & Pwc & Pfc & Psh & Pfs & Pdl & Pwr & Ptp & Pfz & Psplo & Psphi & Pnmax & Ppris & Pkc & Pkr & Pfd).
      clear Rd Rsh Rshm Rshw Wfr Zsh Wsh Rm1 Rm2 Rh Wh Cssl Cngc Zfl Wfl Rfr Wfrm Rfsh Wfsh Ctp Cdb Cbeg Ctsd Cthr Rthr
            Nctx Nthr Db0 Db1 Cx0 Cx1 Th0 Th1 AP1 AP2 AP3 Kc Kg Kp Rpr Wpr Rer Wer H1 H2 H4 H10 H11 Gkcs Ggsh Gtsd Gkc Gkr.
      pose proof usp_range as Usp. pose proof ud_range as Ud. pose proof (u_word_lt (getr regs (Z_to_bv 5 3))) as Ugp.
      fold usp in Hsp16, Hsplo, Hsphi, Hdj1, Hdj2. fold ud in Hd0, Hdn, Hd16, Hdhi, Hdj1, Hdj3.
      unfold LOWMEM_TOP, HIGHMEM_LO, VA_HI, FContractAsan.F_SPLO, FContractAsan.F_SPHI, FS_LEN in *.
      split; [|split; [|split; [|split]]].
      - (* [comment removed for export] *)
        clear Hdj1 Hdj2 Hdj3 Hdhi. unfold env_ok. cbn [ev1 E2 rootE2 rootE e_sp0 e_size e_data e_ra e_tp e_gp e_sregs fp_of_fa fp_ret fp_tp].
        rewrite Pfr, Psplo, Psphi, Pnmax. fold usp ud.
        clear - Hsp16 Hsplo Hsphi Hn Hd0 Hdn Gnmax Gsplo Gsphi Gsphi' Gret Gret2 Gtp0 Gtp1 Gtsd1 F32 F64' Usp Ud Ugp.
        repeat split; try (simpl; reflexivity); (ltac2:(LK.k [@Gret; @Hd0; @Hsp16; @Hsplo; @Ud; @Gsplo; @Gsphi; @Hsphi; @Hn; @Gnmax; @Hdn; @Gtp0; @Gtp1; @Gtsd1; @Ugp; @F32]); lia).
      - (* [comment removed for export] *)
        unfold env_data2. cbn [ev1 E2 rootE2 rootE e_data e_args]. rewrite Pdl. fold ud.
        split; [exact Hd16|]. split; [lia|]. split; [|reflexivity].
        intros _. apply Z.mod_divide in Hd16 as [q Hq]; [|lia]. rewrite Hq. replace (q * 16) with ((q * 2) * 8) by lia. apply Z_mod_mult.
      - (* [comment removed for export] *)
        unfold env_fs. rewrite Pfs. cbn [ev1 E2 rootE2 rootE e_sp0 e_size e_data e_fs e_live]. rewrite Pfr, Pdl. fold usp ud.
        unfold off_band, LOW_MEM_TOP, HIGH_MEM_BEG, HIGH_MEM_END, FS_FRAMES, FS_NCLASSES, FS_SSL.
        split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact Hfs4|]. split; [simpl; lia|].
        split; [constructor|]. split; [constructor|].
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [intros; liae|].
        split.
        { intros _ Hpos a Ha. rewrite Psh in Ha.
          destruct (in_rw_zones P E2 a) eqn:Z; [exfalso|reflexivity].
          apply rw_zone_cases in Z. unfold FS_HINTS, FContractAsan.FS_FLAGS, FS_FLAGS_LEN, FContractAsan.FS_FRAMES, FS_FRAMES_LEN in Z.
          assert (D1 : 2 <= ud / 8) by (apply Z.div_le_lower_bound; liae).
          assert (D2 : (ud + n - 1) / 8 <= 17592186044416 - 9) by (apply Z.div_le_upper_bound; (ltac2:(LK.k [@Gsh'; @F64'; @Hd0; @Hd16; @Hdhi; @Hsplo; @Hsphi; @Hfslo; @Hfshi; @Hdj1; @Hdj2; @Hdj3; @Hpos; @Ha; @Z; @H; @H0; @H4; @H5; @H14; @H15; @H19; @H20; @H24; @H25; @H29; @H30; @H49]); liae)).
          destruct Z as [Z|[Z|[Z|[Z|Z]]]]; [| (ltac2:(LK.k [@Gsh'; @F64'; @Gret; @Hd0; @Hsplo; @Hfslo; @Hdj3; @Ud; @Hpos; @Ha; @Z; @D1; @D2]); lia) | (ltac2:(LK.k [@Gsh'; @F64'; @Gret; @Hd0; @Hsplo; @Hfslo; @Hdj3; @Ud; @Hpos; @Ha; @Z; @D1; @D2]); lia) | (ltac2:(LK.k [@Gsh'; @F64'; @Gret; @Hd0; @Hsplo; @Hfslo; @Hdj3; @Ud; @Hpos; @Ha; @Z; @D1; @D2]); lia) |].
          - (* [comment removed for export] *)
            destruct Hdj1 as [X|X].
            + assert ((ud + n - 1) / 8 + 9 <= (usp - fa_frame FA) / 8) by
                (apply Z.div_le_lower_bound; [(ltac2:(LK.k [@F64'; @F32; @Gret; @Hd0; @Hsplo; @Hfslo; @X; @Hdj2; @Hdj3; @Ud; @Hpos; @H]); lia)|]; pose proof (Z.mul_div_le (ud + n - 1) 8 ltac:((ltac2:(LK.k [@F64'; @F32; @Gret; @Hd0; @Hsplo; @Hfslo; @X; @Hdj2; @Hdj3; @Ud; @Hpos; @H]); lia))); (ltac2:(LK.k [@F64'; @F32; @Gret; @Hd0; @Hsplo; @Hfslo; @X; @Hdj2; @Hdj3; @Ud; @Hpos; @H]); lia)).
              assert ((usp - fa_frame FA) / 8 <= usp / 8 - fa_frame FA / 8).
              { apply Z.mod_divide in F64 as [q Hq]; [|lia]. rewrite Hq. replace (usp - q * 64) with (usp + (- (q * 8)) * 8) by lia.
                rewrite Z.div_add by lia. replace (q * 64) with ((q * 8) * 8) by lia. rewrite Z.div_mul by lia. lia. }
              (ltac2:(LK.k [@F64'; @F32; @Gret; @Gtp1; @Gpr0; @Gpr1; @Gimg1; @Hd0; @Hsplo; @Hfslo; @Hfsimg; @X; @Ud; @Hpos; @Ha; @Z; @H; @H0]); lia).
            + assert (usp / 8 + 8 <= ud / 8) by (apply Z.div_le_lower_bound; [(ltac2:(LK.k [@F64'; @Gret; @Hd0; @Hsplo; @Hfslo; @X; @Hdj2; @Hdj3; @Ud; @Hpos; @H]); lia)|]; pose proof (Z.mul_div_le usp 8 ltac:((ltac2:(LK.k [@F64'; @Gret; @Hd0; @Hsplo; @Hfslo; @X; @Hdj2; @Hdj3; @Ud; @Hpos; @H]); lia))); (ltac2:(LK.k [@F64'; @Gret; @Hd0; @Hsplo; @Hfslo; @X; @Hdj2; @Hdj3; @Ud; @Hpos; @H]); lia)). (ltac2:(LK.k [@F64'; @Gret; @Gtp1; @Gpr0; @Gpr1; @Gimg1; @Hd0; @Hsplo; @Hfslo; @Hfsimg; @X; @Hdj2; @Ud; @Hpos; @Ha; @Z; @H]); lia).
          - destruct Hdj3 as [X|X].
            + assert (fs / 8 + 1446400 + 512 - 8 <= ud / 8 - 8); [|(ltac2:(LK.k [@F64'; @Hd0; @Hd16; @Hdhi; @Hsplo; @Hfslo; @Hdj1; @Hdj2; @X; @H67; @Hpos; @Ha; @Z; @H0; @H1; @H5; @H6; @H15; @H16; @H20; @H21; @H45]); liae)].
              assert ((fs + 11571200 + 4096) / 8 <= ud / 8) by (apply Z.div_le_mono; lia).
              replace (fs + 11571200 + 4096) with (fs + (1446400 + 512) * 8) in H by lia. rewrite Z.div_add in H by lia. lia.
            + assert ((ud + n - 1) / 8 < fs / 8 + 1) by (apply Z.div_lt_upper_bound; [(ltac2:(LK.k [@F64'; @Hd0; @Hdhi; @Hsplo; @Hfs4; @Hfslo; @Hdj1; @Hdj2; @X; @H67; @Hpos; @Ha; @Z; @H0; @H1; @H5; @H6; @H15; @H16; @H35]); lia)|]; pose proof (Z.mul_div_le fs 8 ltac:((ltac2:(LK.k [@F64'; @Hd0; @Hdhi; @Hsplo; @Hfs4; @Hfslo; @Hdj1; @Hdj2; @X; @H67; @Hpos; @Ha; @Z; @H0; @H1; @H5; @H6; @H15; @H16; @H35]); lia))); (ltac2:(LK.k [@F64'; @Hd0; @Hdhi; @Hsplo; @Hfs4; @Hfslo; @Hdj1; @Hdj2; @X; @H67; @Hpos; @Ha; @Z; @H0; @H1; @H5; @H6; @H15; @H16; @H35]); liae)). (ltac2:(LK.k [@F64'; @Hd0; @Hdhi; @Hsplo; @Hfs4; @Hfslo; @Hdj1; @Hdj2; @X; @H67; @Hpos; @Ha; @Z; @H0; @H1; @H5; @H6; @H15; @H16; @H35]); liae). }
        split; [lia|]. split; [cbn [length]; exact Pfd|].
        (* [comment removed for export] *)
        unfold P, unit_params2. cbn [vp_imgend]. rewrite Gimg. exact Hfsimg.
      - (* [comment removed for export] *)
        clear Hdj1.
        unfold env_zones. cbn [ev1 E2 rootE2 rootE e_sp0 e_size e_data]. rewrite Pfr, Pfc, Ppris. fold usp ud.
        assert (U8 : 17591917604864 <= usp / 8 <= 17592186044414) by (split; [apply Z.div_le_lower_bound|apply Z.div_le_upper_bound]; lia).
        assert (F8 : 0 <= fs / 8 <= 17592186044416 - 1446400) by (split; [apply Z.div_pos|apply Z.div_le_upper_bound]; lia).
        assert (R8 : 8 <= fa_frame FA / 8 <= 536870912) by (split; [apply Z.div_le_lower_bound|apply Z.div_le_upper_bound]; lia).
        split.
        + intros z Hz. pose proof (zone_bounds z Hz) as ZB. cbv zeta in ZB.
          unfold FS_HINTS, FContractAsan.FS_FLAGS, FS_FLAGS_LEN, FContractAsan.FS_FRAMES, FS_FRAMES_LEN in ZB.
          clear - ZB U8 F8 R8 Gsh' Hfslo Hfshi.
          destruct ZB as [(L & H & _)|[(L & H & _)|[(L & H & _)|[(L & H & _)|[(L & H & _)|[(L & H & _)|[(L & H & _)|[(L & H & _)|(L & H & _)]]]]]]]];
            rewrite L, H; liae.
        + intros z a Hz Ha. unfold in_zone in Ha. pose proof (zone_bounds z Hz) as ZB. cbv zeta in ZB.
          unfold FS_HINTS, FContractAsan.FS_FLAGS, FS_FLAGS_LEN, FContractAsan.FS_FRAMES, FS_FRAMES_LEN in ZB.
          assert (PRIS : forall lo hi, In (lo, hi) (vp_pristine (p1 (ge2_P0 G))) -> hi <= 2147446784 /\ hi <= fa_imgend FA).
          { intros lo hi Hin. destruct (Gpris _ Hin) as (r' & Hr' & _ & X2). destruct (Gprs _ Hr') as [_ X3]. specialize (Gimg2 _ Hr').
            cbn [snd] in X2. clear - X2 X3 Gimg2. lia. }
          clear - ZB Ha Usp U8 F8 R8 Hsplo Hsphi Hfslo Hfshi Hfsimg Hdj2 Hdj3 Hdhi Hn Gsh' Gpr0 Gpr1 Ger0 Ger1 Gtp0 Gtp1 Gtsd0 Gtsd1 Gimg0 Gimg1 F32 PRIS.
          destruct ZB as [(L & H & R)|[(L & H & R)|[(L & H & R)|[(L & H & R)|[(L & H & R)|[(L & H & R)|[(L & H & R)|[(L & H & R)|(L & H & R)]]]]]]]];
            rewrite L, H in Ha; (split; [(ltac2:(LK.k [@Gsh'; @F32; @Hsplo; @U8; @Ha; @R8; @Hdj2; @H27; @Hfshi; @H0; @H1; @H5; @H6; @H10; @H11; @H22; @Gtp1; @Gpr1; @Gtsd1; @Gimg1; @Hfslo; @Hfsimg; @Ger1; @F8; @PRIS]); liae)|]); (split; [intros c [<-|[<-|[]]]; cbn [fst snd]; (ltac2:(LK.k [@Gsh'; @F32; @Hsplo; @U8; @Ha; @R8; @Hdj2; @H27; @Hfshi; @H0; @H1; @H5; @H6; @H10; @H11; @H22; @Gtp1; @Gpr1; @Gtsd1; @Gimg1; @Hfslo; @Hfsimg; @Ger1; @F8; @PRIS]); lia)|]);
            (split; [intros Hrw; try (rewrite Hrw in R; discriminate)|intros lo hi Hin; specialize (PRIS _ _ Hin); (ltac2:(LK.k [@Gsh'; @F32; @Hsplo; @U8; @Ha; @R8; @Hdj2; @H27; @Hfshi; @H0; @H1; @H5; @H6; @H10; @H11; @H22; @Gtp1; @Gpr1; @Gtsd1; @Gimg1; @Hfslo; @Hfsimg; @Ger1; @F8; @PRIS]); lia)]).
          * destruct (Z.lt_ge_cases 0 n); [specialize (Hdhi ltac:(lia)); lia|lia].
          * lia.
          * lia.
          * lia.
          * destruct (Z.lt_ge_cases 0 n); [specialize (Hdhi ltac:(lia)); liae|lia].
      - (* [comment removed for export] *)
        pose proof GOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Gkc & Gkr & _
                        & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Gkcs & Ggsh & _).
        clear Hdj1 Hdj2 Hdj3 Hdhi.
        unfold env_kcells. cbn [ev1 E2 rootE2 rootE e_sp0]. rewrite Pfr, Pkc, Pkr, Gkc, Gkr. fold usp. split.
        + intros c x Hc Hx. apply in_map_iff in Hc as (c0 & <- & Hc0). cbn [fst snd] in Hx. destruct (Gkcs _ Hc0) as (K1 & K2 & K3 & K4).
          pose proof (Gimg3 _ Hc0) as K5.
          split; [|lia]. destruct (in_rw_zones P E2 x) eqn:Z; [exfalso|reflexivity]. apply rw_zone_cases in Z.
          unfold FS_HINTS, FContractAsan.FS_FLAGS, FS_FLAGS_LEN, FContractAsan.FS_FRAMES, FS_FRAMES_LEN in Z.
          assert (17591917604864 <= usp / 8) by (apply Z.div_le_lower_bound; lia). assert (0 <= fs / 8) by (apply Z.div_pos; lia).
          assert (fa_frame FA / 8 <= 536870912) by (apply Z.div_le_upper_bound; lia). (ltac2:(LK.k [@Gsh'; @F64'; @Gret; @Gtp1; @Gpr0; @Gpr1; @Gimg1; @Gimg5; @Hd0; @Hsplo; @Hfslo; @Hfsimg; @Ud; @Hx; @K3; @K5; @Z; @H; @H0; @H1]); lia).
        + intros c x Hc Hx. apply in_map_iff in Hc as (c0 & <- & Hc0). cbn [fst snd] in Hx. destruct (Ggsh _ Hc0) as (K1 & K2 & K3 & K4).
          pose proof (Gimg4 _ Hc0) as K5.
          split; [lia|]. split; [|lia]. destruct (in_rw_zones P E2 x) eqn:Z; [exfalso|reflexivity]. apply rw_zone_cases in Z.
          unfold FS_HINTS, FContractAsan.FS_FLAGS, FS_FLAGS_LEN, FContractAsan.FS_FRAMES, FS_FRAMES_LEN in Z.
          assert (17591917604864 <= usp / 8) by (apply Z.div_le_lower_bound; lia). assert (0 <= fs / 8) by (apply Z.div_pos; lia).
          assert (fa_frame FA / 8 <= 536870912) by (apply Z.div_le_upper_bound; lia).
          assert (fa_imgend FA / 8 <= fs / 8) by (apply Z.div_le_mono; lia). (ltac2:(LK.k [@Gsh'; @F64'; @Gret; @Gtp1; @Gpr0; @Gpr1; @Gimg0; @Gimg1; @Hd0; @Hsplo; @Hfslo; @Hfsimg; @Ud; @Hx; @K1; @K3; @K5; @Z; @H; @H1; @H2]); lia).
    Qed.
    #[using="Type"] Lemma rt_cell_of mem0 a w v :
      FContractAsan.cell SEGS mem0 a w v -> 0 <= a -> 0 < w -> a + w <= 2 ^ 64 -> rt_apart P E2 a w -> rt_cell SEGS P E2 mem0 a w v.
    Proof. intros H A0 W0 AW AP. split; [exact A0|]. split; [exact W0|]. split; [exact AW|]. split; [exact AP|]. exact H. Qed.

    (* [comment removed for export] *)
    #[using="SEGS GOK RU res mem ctx thr db PRE Hres Hanc usp ud"] Lemma rt_apart_of a w :
      (apart_writes FA (bv_unsigned sp) fs a w
       \/ (0 <= a /\ a + w <= fa_imgend FA /\ (a + w <= fa_prng FA \/ fa_prng FA + 8 <= a) /\ (a + w <= fa_errno FA \/ fa_errno FA + 4 <= a))
       \/ (fs + FS_HINTS <= a /\ a + w <= fs + FContractAsan.FS_FLAGS)) ->
      rt_apart P E2 a w.
    Proof.
      pose proof GOK as (Gfr & Gtp & Gtp' & Gerr & Gfc & Gnmax & Gsplo & Gsphi & Gsphi' & Gpris & Gsh & Gsh' & Gfs & Gdl & Gkc & Gkr & Gfz
                        & F64 & F64' & F32 & Gret2 & Gret & Gtp0 & Gtp1 & Gtp2 & Gpr0 & Gpr1 & Ger0 & Ger1 & Gkcs & Ggsh & Gprs & Gtsd & Gtsd0 & Gtsd1 & Gimg & Gimg0 & Gimg1 & Gimg2 & Gimg3 & Gimg4 & Gimg5).
      pose proof A_PRE as (H1 & H2 & H4 & H10 & H11 & Hn & Hd0 & Hdn & Hd16 & Hdhi & Hsp16 & Hsplo & Hsphi & Hfs4 & Hfslo & Hfshi & Hfsimg
                        & Hdj1 & Hdj2 & Hdj3 & Rd & Rsh & Rshm & Rshw & Wfr & Zsh & Wsh & Rm1 & Rm2 & RZ1 & Rh & Wh & Cssl & Cngc
                        & Zfl & Wfl & Rfr & Wfrm & Rfsh & Wfsh & Ctp & Cdb & Cbeg & Ctsd & Cthr & Rthr
                        & Nctx & Nthr & Db0 & Db1 & Cx0 & Cx1 & Th0 & Th1 & AP1 & AP2 & AP3 & Kc & Kg & Kp & Rpr & Wpr & Rer & Wer).
      destruct P_facts as (Pfr & Pws & Pwc & Pfc & Psh & _).
      fold usp in Hsp16, Hsplo, Hsphi, Hdj1, Hdj2. unfold LOWMEM_TOP, HIGHMEM_LO, VA_HI, FContractAsan.F_SPLO, FContractAsan.F_SPHI, FS_LEN in *.
      intros CASES x Hx. unfold rt_apart. change (e_sp0 (ev1 E2)) with usp. rewrite Pfr, Pfc.
      assert (U8 : 17591917604864 <= usp / 8 <= 17592186044414) by (split; [apply Z.div_le_lower_bound|apply Z.div_le_upper_bound]; lia).
      assert (F8 : 0 <= fs / 8) by (apply Z.div_pos; lia).
      assert (R8 : 8 <= fa_frame FA / 8 <= 536870912) by (split; [apply Z.div_le_lower_bound|apply Z.div_le_upper_bound]; lia).
      assert (SF : (usp - fa_frame FA) / 8 = usp / 8 - fa_frame FA / 8).
      { pose proof F64 as F. apply Z.mod_divide in F as [q Hq]; [|clear; lia]. rewrite Hq. replace (usp - q * 64) with (usp + (- (q * 8)) * 8) by (clear; lia).
        rewrite Z.div_add by (clear; lia). replace (q * 64) with ((q * 8) * 8) by (clear; lia). rewrite Z.div_mul by (clear; lia). clear; lia. }
      assert (SFS : (fs + 36864) / 8 = fs / 8 + 4608).
      { replace (fs + 36864) with (fs + 4608 * 8) by (clear; lia). rewrite Z.div_add by (clear; lia). clear; lia. }
      clear PRE.
      destruct CASES as [AW|[(A0 & A1 & A2 & A3)|[A0 A1]]].
      - unfold apart_writes, FA_writes in AW. cbn [app] in AW. unfold FContractAsan.shadow in AW.
        apply Forall_cons_iff in AW as [W1 AW]. apply Forall_cons_iff in AW as [W2 AW]. apply Forall_cons_iff in AW as [W3 AW].
        apply Forall_cons_iff in AW as [W4 AW]. apply Forall_cons_iff in AW as [W5 AW]. apply Forall_cons_iff in AW as [W6 AW].
        apply Forall_cons_iff in AW as [W7 AW]. apply Forall_cons_iff in AW as [W8 AW].
        apply Forall_cons_iff in AW as [W9 AW]. apply Forall_cons_iff in AW as [W10 _].
        cbn [fst snd] in W1, W2, W3, W4, W5, W6, W7, W8, W9, W10.
        unfold FS_HINTS, FContractAsan.FS_FLAGS, FS_FLAGS_LEN, FContractAsan.FS_FRAMES, FS_FRAMES_LEN in W2, W3, W4, W5, W6.
        (* [comment removed for export] *)
        assert (AN : usp = bv_unsigned sp \/ usp = bv_unsigned sp + 16) by (unfold usp; rewrite Hanc; destruct usp0_cases as [E|E]; rewrite E; lia).
        assert (SFR : (bv_unsigned sp - fa_frame FA) / 8 = bv_unsigned sp / 8 - fa_frame FA / 8).
        { pose proof F64 as F. apply Z.mod_divide in F as [q Hq]; [|clear; lia]. rewrite Hq. replace (bv_unsigned sp - q * 64) with (bv_unsigned sp + (- (q * 8)) * 8) by (clear; lia).
          rewrite Z.div_add by (clear; lia). replace (q * 64) with ((q * 8) * 8) by (clear; lia). rewrite Z.div_mul by (clear; lia). clear; lia. }
        assert (AN8 : usp / 8 = bv_unsigned sp / 8 \/ usp / 8 = bv_unsigned sp / 8 + 2).
        { destruct AN as [E|E]; rewrite E; [left; reflexivity|right]. replace (bv_unsigned sp + 16) with (bv_unsigned sp + 2 * 8) by (clear; lia). apply Z.div_add. clear; lia. }
        rewrite SFR in W2. rewrite SFS in W6.
        split; [|split; [clear - W1 W9 Hx AN; lia|intros c [<-|[<-|[]]]; cbn [fst snd]; [clear - W7 Hx|clear - W8 Hx]; lia]].
        destruct (in_rw_zones P E2 x) eqn:Z; [exfalso|reflexivity]. apply rw_zone_cases in Z.
        unfold FS_HINTS, FContractAsan.FS_FLAGS, FS_FLAGS_LEN, FContractAsan.FS_FRAMES, FS_FRAMES_LEN in Z. clear - Z W2 W3 W4 W5 W6 W10 Hx AN8. (ltac2:(LK.k [@W2; @W3; @W4; @W5; @W6; @W10; @Hx; @AN8; @Z; @H14; @H15]); liae).
      - split; [|split; [clear - A0 A1 Hx Hsplo F32 Gimg5; lia|intros c [<-|[<-|[]]]; cbn [fst snd]; [clear - A2 Hx|clear - A3 Hx]; lia]].
        destruct (in_rw_zones P E2 x) eqn:Z; [exfalso|reflexivity]. apply rw_zone_cases in Z.
        unfold FS_HINTS, FContractAsan.FS_FLAGS, FS_FLAGS_LEN, FContractAsan.FS_FRAMES, FS_FRAMES_LEN in Z. clear - Z A0 A1 Hx U8 F8 R8 Gsh' Hfslo Hfsimg Gimg5. lia.
      - unfold FS_HINTS, FContractAsan.FS_FLAGS in A0, A1.
        split; [|split; [clear - A0 A1 Hx Hdj2 Hfslo; lia|intros c [<-|[<-|[]]]; cbn [fst snd]; [clear - A0 Hx Hfslo Hfsimg Gimg1 Gpr1 Gtp0 Gtsd1 Gtp1|clear - A0 Hx Hfslo Hfsimg Gimg1 Ger1 Gtp0 Gtsd1 Gtp1]; lia]].
        destruct (in_rw_zones P E2 x) eqn:Z; [exfalso|reflexivity]. apply rw_zone_cases in Z.
        unfold FS_HINTS, FContractAsan.FS_FLAGS, FS_FLAGS_LEN, FContractAsan.FS_FRAMES, FS_FRAMES_LEN in Z. clear - Z A0 A1 Hx U8 F8 R8 Gsh' Hfslo Hfshi. liae.
    Qed.

    #[using="GOK RU res sp ctx thr db PRE Hres Hanc usp ud"] Lemma mcE : MC2 SEGS P E2 mem mem.
    Proof.
      pose proof GOK as (Gfr & Gtp & Gtp' & Gerr & Gfc & Gnmax & Gsplo & Gsphi & Gsphi' & Gpris & Gsh & Gsh' & Gfs & Gdl & Gkc & Gkr & Gfz
                        & F64 & F64' & F32 & Gret2 & Gret & Gtp0 & Gtp1 & Gtp2 & Gpr0 & Gpr1 & Ger0 & Ger1 & Gkcs & Ggsh & Gprs & Gtsd & Gtsd0 & Gtsd1 & Gimg & Gimg0 & Gimg1 & Gimg2 & Gimg3 & Gimg4 & Gimg5).
      pose proof A_PRE as (H1 & H2 & H4 & H10 & H11 & Hn & Hd0 & Hdn & Hd16 & Hdhi & Hsp16 & Hsplo & Hsphi & Hfs4 & Hfslo & Hfshi & Hfsimg
                        & Hdj1 & Hdj2 & Hdj3 & Rd & Rsh & Rshm & Rshw & Wfr & Zsh & Wsh & Rm1 & Rm2 & RZ1 & Rh & Wh & Cssl & Cngc
                        & Zfl & Wfl & Rfr & Wfrm & Rfsh & Wfsh & Ctp & Cdb & Cbeg & Ctsd & Cthr & Rthr
                        & Nctx & Nthr & Db0 & Db1 & Cx0 & Cx1 & Th0 & Th1 & AP1 & AP2 & AP3 & Kc & Kg & Kp & Rpr & Wpr & Rer & Wer).
      destruct P_facts as (Pfr & Pws & Pwc & Pfc & Psh & Pfs & Pdl & Pwr & Ptp & Pfz & Psplo & Psphi & Pnmax & Ppris & Pkc & Pkr & Pfd).
      pose proof usp_range as Usp. pose proof ud_range as Ud.
      fold usp in Hsp16, Hsplo, Hsphi, Hdj1, Hdj2, Wfr, Zsh, Wsh, Rm1, Rm2, AP1, AP2, AP3. fold ud in Hd0, Hdn, Hd16, Hdhi, Hdj1, Hdj3, Rd, Rsh, Rshm, Rshw.
      unfold FContractAsan.shadow in Zsh, Wsh, Rm1, Rm2, RZ1, Rsh, Rshm, Rshw, Rfsh, Wfsh.
      unfold LOWMEM_TOP, HIGHMEM_LO, VA_HI, FContractAsan.F_SPLO, FContractAsan.F_SPHI, FS_LEN in *.
      assert (SF : (usp - fa_frame FA) / 8 = usp / 8 - fa_frame FA / 8).
      { pose proof F64 as F. apply Z.mod_divide in F as [q Hq]; [|lia]. rewrite Hq. replace (usp - q * 64) with (usp + (- (q * 8)) * 8) by lia.
        rewrite Z.div_add by lia. replace (q * 64) with ((q * 8) * 8) by lia. rewrite Z.div_mul by lia. lia. }
      assert (SFS : (fs + FContractAsan.FS_FRAMES) / 8 = fs / 8 + FContractAsan.FS_FRAMES / 8).
      { unfold FContractAsan.FS_FRAMES. replace (fs + 36864) with (fs + 4608 * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
      rewrite SF in Zsh, Wsh, Rm1, RZ1. rewrite SFS in Rfsh, Wfsh.
      clear H1 H2 H4 H10 H11.
      split; [|split; [|split; [|split; [|split]]]].
      - (* [comment removed for export] *)
        clear - Pkc Gkc Gkcs Kc.
        intros a w v Hin. rewrite Pkc, Gkc in Hin. apply in_map_iff in Hin as (c & E & Hc). injection E as <- <- <-.
        destruct (Gkcs _ Hc) as (K1 & K2 & K3 & K4). rewrite Forall_forall in Kc. specialize (Kc _ Hc). cbn beta in Kc.
        split; [exact K1|]. split; [lia|]. split; [lia|]. exact (cell_at _ _ _ _ _ Kc ltac:(lia) K4).
      - (* [comment removed for export] *)
        intros z a Hz Ha. unfold in_zone in Ha. pose proof (zone_bounds z Hz) as ZB. cbv zeta in ZB.
        clear - Ha ZB Zsh Wsh Rm1 Rm2 RZ1 Rh Wh Zfl Wfl Rfr Wfrm Rfsh Wfsh.
        unfold FS_HINTS, FContractAsan.FS_FLAGS, FS_FLAGS_LEN, FContractAsan.FS_FRAMES, FS_FRAMES_LEN in *.
        destruct ZB as [(L & H & R)|[(L & H & R)|[(L & H & R)|[(L & H & R)|[(L & H & R)|[(L & H & R)|[(L & H & R)|[(L & H & R)|(L & H & R)]]]]]]]];
          rewrite L, H in Ha; rewrite R.
        + split; [|intros _; eapply writable_at; [exact Wsh|lia]]. eapply readable_at; [exact RZ1|lia].
        + split; [|discriminate]. eapply readable_at; [exact Rm1|lia].
        + split; [|discriminate]. eapply readable_at; [exact Rm2|lia].
        + split; [|intros _; eapply writable_at; [exact Wh|lia]]. eapply readable_at; [exact Rh|lia].
        + split; [|intros _; eapply writable_at; [exact Wfl|lia]]. destruct (zeroes_at _ _ _ _ a Zfl ltac:(lia)) as (b & Hb & _). exists b; exact Hb.
        + split; [|intros _; eapply writable_at; [exact Wfrm|lia]]. eapply readable_at; [exact Rfr|lia].
        + split; [|intros _; eapply writable_at; [exact Wfsh|lia]]. eapply readable_at; [exact Rfsh|lia].
        + split; [|discriminate]. eapply readable_at; [exact Rfsh|lia].
        + split; [|discriminate]. eapply readable_at; [exact Rfsh|lia].
      - (* [comment removed for export] *)
        intros _ _. unfold shadow_byte. cbn [ev1 E2 rootE2 rootE e_data e_size]. rewrite Psh. fold ud.
        assert (D8 : forall k, (ud + k) / 8 = ud / 8 + k / 8).
        { intros k. apply Z.mod_divide in Hd16 as [q Hq]; [|lia]. rewrite Hq. replace (q * 16) with ((q * 2) * 8) by lia.
          rewrite Z.div_mul, Z.add_comm, Z.div_add, Z.add_comm by lia. reflexivity. }
        clear - Rsh Rshm Rshw D8 Hn.
        split; [|split].
        + intros g Hg. specialize (Rsh ltac:(lia) g Hg). eexists. rewrite wordZ_to_bv. split; [exact Rsh|].
          destruct (Z.leb_spec (8 * g + 8) n); rewrite u_Z_to_bv8 by lia; lia.
        + intros a Ha Hpos. eapply readable_at; [exact (Rshm Hpos)|]. replace (ud + n - 1) with (ud + (n - 1)) in Ha by lia. rewrite D8 in Ha.
          assert ((n - 1) / 8 <= n / 8) by (apply Z.div_le_mono; lia). clear - Ha H. lia.
        + intros Hpos a Ha. eapply readable_at; [exact (Rshw Hpos)|]. unfold rd8 in *.
          pose proof (Z.div_mod (fa_shoff FA + ud / 8) 8 ltac:(lia)) as M1. pose proof (Z.div_mod (fa_shoff FA + (ud + n - 1) / 8) 8 ltac:(lia)) as M2.
          clear - Ha M1 M2. lia.
      - (* [comment removed for export] *)
        intros cp [].
      - (* [comment removed for export] *)
        clear Rd Rsh Rshm Rshw Wfr Zsh Wsh Rm1 Rm2 Rh Wh Zfl Wfl Rfr Wfrm Rfsh Wfsh Kg Kp Rpr Wpr Rer Wer Hdj1 Hdj3 Hdhi Hd0 Hdn Hd16.
        unfold rtctx_ok. rewrite Pfs. cbn [e_fs E2 rootE2]. rewrite Ptp.
        assert (TSD : FContractAsan.cell SEGS mem (fa_tp FA - 88) 8 (fa_tsd FA)).
        { rewrite Forall_forall in Kc. exact (Kc _ Gtsd). }
        exists (fa_tsd FA), ctx, thr, db, (fa_tp FA).
        unfold FContractAsan.FS_SSL in Cssl. unfold FContractAsan.FS_NEEDSGC in Cngc. unfold VGamma2.FS_SSL.
        split. { apply (rt_cell_of _ _ _ _ Ctp); [lia|lia|lia|]. apply rt_apart_of. right; left. lia. }
        split. { apply (rt_cell_of _ _ _ _ Cssl); [lia|lia|lia|]. apply rt_apart_of. right; right. unfold FS_HINTS, FContractAsan.FS_FLAGS. lia. }
        split. { apply (rt_cell_of _ _ _ _ Cngc); [lia|lia|lia|]. apply rt_apart_of. right; right. unfold FS_HINTS, FContractAsan.FS_FLAGS. lia. }
        split. { apply (rt_cell_of _ _ _ _ TSD); [lia|lia|lia|]. apply rt_apart_of. right; left. lia. }
        split. { apply (rt_cell_of _ _ _ _ Ctsd); [lia|lia|lia|]. apply rt_apart_of. right; left. lia. }
        split; [lia|].
        split. { apply (rt_cell_of _ _ _ _ Cthr); [lia|lia|lia|]. apply rt_apart_of. left. exact AP2. }
        split; [lia|].
        split. { split; [lia|]. split; [lia|]. split; [apply rt_apart_of; left; exact AP3|].
                 intros i Hi. eapply readable_at; [exact Rthr|lia]. }
        split. { apply (rt_cell_of _ _ _ _ Cdb); [lia|lia|lia|]. apply rt_apart_of. right; left. lia. }
        split; [lia|]. split; [lia|].
        split. { apply (rt_cell_of _ _ _ _ Cbeg); [lia|lia|lia|]. apply rt_apart_of. left. exact AP1. }
        lia.
      - (* [comment removed for export] *)
        clear - Pkr Gkr Ggsh Kg Gsh'. intros lo hi b Hin. rewrite Pkr, Gkr in Hin. apply in_map_iff in Hin as (r & E & Hr). injection E as <- <- <-.
        destruct (Ggsh _ Hr) as (K1 & K2 & K3). rewrite Forall_forall in Kg. specialize (Kg _ Hr). cbn beta in Kg.
        destruct K3 as [K3 K4].
        split; [lia|]. split; [lia|]. intros a Ha. eapply filled_at; [exact Kg|exact K4|lia].
    Qed.
    (* [comment removed for export] *)
    #[using="SEGS G GOK RU res mem sp ctx thr db PRE Hcls Hres Hanc usp ud"] Lemma canon_store2_sat : sat nu (canon_store2 cls).
    Proof.
      pose proof A_PRE as (H1 & H2 & H4 & H10 & H11 & Hn & Hd0 & Hdn & Hd16 & Hdhi & Hsp16 & Hsplo & Hsphi & Hfs4 & Hfslo & Hfshi & Hfsimg
                        & Hdj1 & Hdj2 & Hdj3 & Rd & Rsh & Rshm & Rshw & Wfr & Zsh & Wsh & Rm1 & Rm2 & RZ1 & Rh & Wh & Cssl & Cngc
                        & Zfl & Wfl & Rfr & Wfrm & Rfsh & Wfsh & Ctp & Cdb & Cbeg & Ctsd & Cthr & Rthr
                        & Nctx & Nthr & Db0 & Db1 & Cx0 & Cx1 & Th0 & Th1 & AP1 & AP2 & AP3 & Kc & Kg & Kp & Rpr & Wpr & Rer & Wer).
      pose proof usp_range as Usp. pose proof ud_range as Ud.
      fold usp in Hsp16, Hsplo, Hsphi. fold ud in Hd0, Hdn, Hd16, Hdhi.
      assert (NS : nu SP0 = usp) by reflexivity. assert (ND : nu DATA = ud) by reflexivity.
      assert (NZ : nu SIZE = n) by reflexivity. assert (NF : nu FSB = fs) by reflexivity.
      unfold canon_store2. unfold LOWMEM_TOP, HIGHMEM_LO, VA_HI, FContractAsan.F_SPLO, FContractAsan.F_SPHI, FS_LEN in *.
      assert (DHI : ud <= (2 ^ 63 - 1 - fst cls) / 16 * 16).
      { clear - Hd16 Hdn Hcls Hn. apply Z.mod_divide in Hd16 as [q Hq]; [|lia]. rewrite Hq.
        assert (q <= (2 ^ 63 - 1 - fst cls) / 16) by (apply Z.div_le_lower_bound; lia). lia. }
      assert (FS0 : 0 <= fs).
      { pose proof GOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Gimg0 & _).
        clear - Gimg0 Hfsimg. lia. }
      pose proof usp_res as URES.
      clear - NS ND NZ NF DHI Hd0 Hdn Hd16 Hsplo Hsphi Hfs4 Hfslo Hfshi FS0 Hn Hcls URES Usp Ud.
      split; [|split].
      - intros s0 i Hg. apply pm_of_list_get_in in Hg. simpl in Hg.
        destruct Hg as [Hg|[Hg|[Hg|[Hg|[]]]]]; injection Hg as <- <-; split; simpl; rewrite ?NS, ?ND, ?NZ, ?NF; unfold cls in *; liae.
      - constructor; [|constructor]. rewrite eval_lsub, eval_ladd, !eval_lsym, eval_lconst, ND, NZ. lia.
      - intros s0 m r Hg. apply pm_of_list_get_in in Hg. simpl in Hg.
        destruct Hg as [Hg|[Hg|[Hg|[]]]]; injection Hg as <- <- <-; rewrite ?NS, ?ND, ?NF.
        + exists (usp / 32). rewrite <- URES. pose proof (Z.div_mod usp 32 ltac:(lia)). lia.
        + exists (ud / 16). pose proof (Z.div_mod ud 16 ltac:(lia)). lia.
        + exists (fs / 4096). pose proof (Z.div_mod fs 4096 ltac:(lia)). lia.
    Qed.

    #[using="SEGS GOK RU res mem sp ctx thr db PRE Hres Hanc usp ud"] Lemma root_regs_sound2 :
      root_regs_ok2 FP (u_sp (u1 U)) (vs_regs (load_cstate (c1 (u2_pre U)) 0 [])) = true ->
      gamma_regs nu (v1 S) regs.
    Proof.
      pose proof A_PRE as (H1 & H2 & H4 & H10 & H11 & Hn & Hd0 & Hdn & Hd16 & Hdhi & Hsp16 & Hsplo & Hsphi & Hfs4 & Hfslo & Hfshi & Hfsimg
                        & Hdj1 & Hdj2 & Hdj3 & Rd & Rsh & Rshm & Rshw & Wfr & Zsh & Wsh & Rm1 & Rm2 & RZ1 & Rh & Wh & Cssl & Cngc
                        & Zfl & Wfl & Rfr & Wfrm & Rfsh & Wfsh & Ctp & Cdb & Cbeg & Ctsd & Cthr & Rthr
                        & Nctx & Nthr & Db0 & Db1 & Cx0 & Cx1 & Th0 & Th1 & AP1 & AP2 & AP3 & Kc & Kg & Kp & Rpr & Wpr & Rer & Wer).
      rewrite <- (reg_lit 1%bv 1 eq_refl) in H1. rewrite <- (reg_lit 2%bv 2 eq_refl) in H2. rewrite <- (reg_lit 4%bv 4 eq_refl) in H4.
      rewrite <- (reg_lit 10%bv 10 eq_refl) in H10. rewrite <- (reg_lit 11%bv 11 eq_refl) in H11.
      intros H r e Hr0 Hget.
      change (vs_regs (v1 S)) with (vs_regs (load_cstate (c1 (u2_pre U)) 0 [])) in Hget.
      unfold root_regs_ok2 in H. rewrite forallb_forall in H.
      remember (bv_unsigned r) as k eqn:Hk.
      assert (Hin : In k (zseq 1 31)) by (apply zseq_in; pose proof (reg_range r); simpl; lia).
      specialize (H k Hin). cbn beta in H. rewrite Hget in H.
      destruct (root_reg2 FP (u_sp (u1 U)) k) as [l|] eqn:R; [|discriminate]. apply lin_eqb_eq in H. subst e.
      rewrite (bv5_of_Z r k (eq_sym Hk)). clear Hr0 Hk Hget Hin.
      unfold root_reg2, root_reg, FP, fp_of_fa in R. cbn [fp_ret fp_tp] in R.
      destruct (Z.eqb_spec k 2).
      { injection R as <-. subst k. rewrite eval_lsymc. rewrite H2. change (nu SP0) with usp. unfold usp. rewrite Hanc.
        replace (bv_unsigned sp - u_sp (u1 U) + u_sp (u1 U)) with (bv_unsigned sp) by lia. symmetry; apply zwrap64_u. }
      destruct (Z.eqb_spec k 1).
      { injection R as <-. subst k. rewrite eval_lconst. rewrite H1. apply u_Z_to_bv64. }
      destruct (Z.eqb_spec k 3).
      { injection R as <-. subst k. rewrite eval_lsym. change (nu GP) with (bv_unsigned (getr regs (Z_to_bv 5 3))). symmetry; apply zwrap64_u. }
      destruct (Z.eqb_spec k 4).
      { injection R as <-. subst k. rewrite eval_lconst. rewrite H4. apply u_Z_to_bv64. }
      destruct (Z.eqb_spec k 10).
      { injection R as <-. subst k. rewrite eval_lsym. rewrite H10. change (nu DATA) with ud. symmetry; apply zwrap64_u. }
      destruct (Z.eqb_spec k 11).
      { injection R as <-. subst k. rewrite eval_lsym. rewrite H11. change (nu SIZE) with n. apply u_Z_to_bv64. }
      destruct (find (fun p : Z * Z => Z.eqb (fst p) k) sreg_idx) as [[r' i]|] eqn:F; [|discriminate].
      apply find_some in F as [Fin Fk]. simpl in Fk. apply Z.eqb_eq in Fk. subst r'.
      injection R as <-. rewrite eval_lsym. unfold nu, E2. rewrite (rootnu2_SREG FA regs spa data n fs _ _ Fin). symmetry; apply zwrap64_u.
    Qed.

    (* [comment removed for export] *)
    #[using="GOK WR RU STATIC cls res FP sp ctx thr db PRE Hcls Hres Hanc usp ud"] Lemma v1E : gamma SEGS (p1 P) (ev1 E2) (zpatch P E2 mem mem) (v1 S) nu regs mem.
    Proof.
      pose proof GOK as (Gfr & Gtp & Gtp' & Gerr & Gfc & Gnmax & Gsplo & Gsphi & Gsphi' & Gpris & Gsh & Gsh' & Gfs & Gdl & Gkc & Gkr & Gfz
                        & F64 & F64' & F32 & Gret2 & Gret & Gtp0 & Gtp1 & Gtp2 & Gpr0 & Gpr1 & Ger0 & Ger1 & Gkcs & Ggsh & Gprs & Gtsd & Gtsd0 & Gtsd1 & Gimg & Gimg0 & Gimg1 & Gimg2 & Gimg3 & Gimg4 & Gimg5).
      pose proof A_PRE as (H1 & H2 & H4 & H10 & H11 & Hn & Hd0 & Hdn & Hd16 & Hdhi & Hsp16 & Hsplo & Hsphi & Hfs4 & Hfslo & Hfshi & Hfsimg
                        & Hdj1 & Hdj2 & Hdj3 & Rd & Rsh & Rshm & Rshw & Wfr & Zsh & Wsh & Rm1 & Rm2 & RZ1 & Rh & Wh & Cssl & Cngc
                        & Zfl & Wfl & Rfr & Wfrm & Rfsh & Wfsh & Ctp & Cdb & Cbeg & Ctsd & Cthr & Rthr
                        & Nctx & Nthr & Db0 & Db1 & Cx0 & Cx1 & Th0 & Th1 & AP1 & AP2 & AP3 & Kc & Kg & Kp & Rpr & Wpr & Rer & Wer).
      destruct P_facts as (Pfr & Pws & Pwc & Pfc & Psh & Pfs & Pdl & Pwr & Ptp & Pfz & Psplo & Psphi & Pnmax & Ppris & Pkc & Pkr & Pfd).
      destruct (root_ok2_facts _ _ RU) as (Rroot & Rentry & Rsp & Rws & Rwg & _ & Rcls & Rpre & Rex).
      destruct (root_pre_ok2_facts _ _ _ _ Rpre) as (Pregs & Psl & Pgl & Pnul & Pvs & Pcd & Pmd & Ple & Plv & Pdd & _).
      pose proof usp_range as Usp. pose proof ud_range as Ud. pose proof (u_word_lt (getr regs (Z_to_bv 5 3))) as Ugp.
      fold usp in Hsp16, Hsplo, Hsphi, Hdj1, Hdj2, Wfr. fold ud in Hd0, Hdn, Hd16, Hdhi, Hdj1, Hdj3, Rd.
      unfold LOWMEM_TOP, HIGHMEM_LO, VA_HI, FContractAsan.F_SPLO, FContractAsan.F_SPHI, FS_LEN in *.
      assert (WF1 : cstate_wf (c1 (u2_pre U)) = true).
      { unfold unit_static_ok2 in STATIC.
        destruct (cstate2_ok P (u2_pre U) && cstate2_iface_b (u2_pre U) && wrgn_ok U (u2_pre U)) eqn:C0; [|discriminate].
        apply andb_prop in C0 as [C0 _]. apply andb_prop in C0 as [C0 _]. destruct (cstate2_ok_parts _ _ C0) as (_ & WF & _).
        exact (proj1 (cstate2_wf_parts _ WF)). }
      split.
      { exact (proj1 envE). }
      split.
      { (* [comment removed for export] *)
        unfold MC. cbn [ev1 E2 rootE2 rootE e_sp0 e_size e_data]. rewrite Pfr, Ppris. fold usp ud.
        split; [|split; [|split]].
        - apply frame_store_ok_readable; auto; [| lia|lia]. intros a Ha. rewrite <- (wordZ_u a). eapply writable_at; [exact Wfr|lia].
        - intros i Hi. eapply readable_at; [exact Rd|lia].
        - intros lo hi a Hin Ha. destruct (Gpris _ Hin) as (r' & Hr' & L1 & L2). cbn [fst snd] in L1, L2. destruct (Gprs _ Hr') as [L3 L4].
          rewrite Forall_forall in Kp. specialize (Kp _ Hr'). apply Kp. rewrite u_wordZ; (ltac2:(LK.k [@F64'; @Hn; @Hd0; @Hsplo; @Hdj1; @Hdj2; @Hdj3; @Nctx; @Nthr; @Cx0; @Th0; @Ud; @Ha; @L1; @L2; @L3; @L4]); lia).
        - eapply frame_mod_mem0_ext; [|apply frame_mod_refl]. intros a. unfold zpatch. destruct (in_rw_zones P E2 (bv_unsigned a)); reflexivity. }
      split; [exact (gamma_fix2_fix _ _ (rootnu2_fix E2))|].
      split.
      { (* [comment removed for export] *)
        cbn [v1 S load_cstate2 vs_store load_cstate]. eapply store_le_sound; [exact Ple|]. exact canon_store2_sat. }
      split.
      { intros b k x y Hg. cbn [v1 S load_cstate2 vs_conddef load_cstate] in Hg. rewrite Pcd in Hg. simpl in Hg. discriminate. }
      split.
      { intros r x m Hg. cbn [v1 S load_cstate2 vs_moddef load_cstate] in Hg. rewrite Pmd in Hg. simpl in Hg. discriminate. }
      split.
      { intros s0 vs Hg. cbn [v1 S load_cstate2 vs_valset load_cstate] in Hg. rewrite Pvs in Hg. simpl in Hg. discriminate. }
      split; [exact (root_regs_sound2 Pregs)|].
      split.
      { intros off w v Hin. cbn [v1 S load_cstate2 vs_slots load_cstate] in Hin. rewrite Psl in Hin. destruct Hin. }
      split.
      { intros a w v Hin. cbn [v1 S load_cstate2 vs_globs load_cstate] in Hin. rewrite Pgl in Hin. destruct Hin. }
      split.
      { intros lo hi Hin. cbn [v1 S load_cstate2 vs_nul load_cstate] in Hin. rewrite Pnul in Hin. destruct Hin. }
      apply (proj1 (load_cstate_below _ _ _ WF1)).
    Qed.
    (* [comment removed for export] *)
    #[using="Type"] Lemma in_any_zone_intro z a : In z (vp_fzones P) -> zone_lo E2 z <= a < zone_hi E2 z -> in_any_zone P E2 a = true.
    Proof. intros Hz Ha. unfold in_any_zone. apply existsb_exists. exists z. split; [exact Hz|]. apply in_zoneb_spec. exact Ha. Qed.
    #[using="Type"] Lemma in_rw_zones_intro z a : In z (vp_fzones P) -> fz_rw z = true -> zone_lo E2 z <= a < zone_hi E2 z -> in_rw_zones P E2 a = true.
    Proof.
      intros Hz Hrw Ha. unfold in_rw_zones, rw_zones. apply existsb_exists. exists z. split; [apply filter_In; auto|]. apply in_zoneb_spec. exact Ha.
    Qed.

    (* [comment removed for export] *)
    #[using="GOK RU STATIC"] Lemma S_rgn : exists s, cs_rgn (u2_pre U) = [s] /\ root_shf_ok (fa_frame FA) (u_sp (u1 U)) s = true
                            /\ vs_rgn S = [vregion_of s; SHD P; FSR]
                            /\ sr_disp s = vp_shoff P /\ sr_lo s = - (fa_frame FA / 8) - 8 /\ sr_hi s = 1 /\ sr_w s = [(- fa_frame FA / 8, u_sp (u1 U) / 8)].
    Proof.
      destruct (root_ok2_facts _ _ RU) as (Rroot & Rentry & Rsp & Rws & Rwg & _ & Rcls & Rpre & Rex).
      destruct (root_pre_ok2_facts _ _ _ _ Rpre) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & s & Es & SHF).
      destruct (root_shf_ok_facts _ _ _ SHF) as (K & B & N & B8 & C).
      destruct P_facts as (Pfr & Pws & Pwc & Pfc & Psh & Pfs & _).
      exists s. split; [exact Es|]. split; [exact SHF|]. split.
      { unfold S, load_cstate2. cbn [vs_rgn]. unfold load_regions, std_regions, has_asan. rewrite Es, Pfs. reflexivity. }
      unfold unit_static_ok2 in STATIC.
      destruct (cstate2_ok P (u2_pre U) && cstate2_iface_b (u2_pre U) && wrgn_ok U (u2_pre U)) eqn:C0; [|discriminate].
      apply andb_prop in C0 as [C0 _]. apply andb_prop in C0 as [C0 _]. destruct (cstate2_ok_parts _ _ C0) as (_ & _ & C3).
      apply andb_prop in C3 as [_ SD]. unfold shadow_disp_ok in SD. rewrite forallb_forall in SD. specialize (SD s ltac:(rewrite Es; left; reflexivity)).
      rewrite K, B, Pos.eqb_refl in SD. cbn [negb orb] in SD.
      apply andb_prop in SD as [SD1 SD2]. apply andb_prop in SD2 as [SD2 W]. apply andb_prop in SD2 as [SD2 HI]. apply andb_prop in SD2 as [_ LO].
      apply Z.eqb_eq in SD1. apply Z.eqb_eq in LO. apply Z.eqb_eq in HI. apply ranges_eqb_eq in W.
      rewrite Pws in W. cbn in W. rewrite Pfr in LO.
      split; [exact SD1|]. split; [exact LO|]. split; [exact HI|]. rewrite W. reflexivity.
    Qed.

    #[using="GOK RU STATIC res sp ctx thr db PRE Hres Hanc usp ud"] Lemma rgnE r : In r (vs_rgn S) -> region_ok SEGS P E2 nu S mem r.
    Proof.
      pose proof GOK as (Gfr & Gtp & Gtp' & Gerr & Gfc & Gnmax & Gsplo & Gsphi & Gsphi' & Gpris & Gsh & Gsh' & Gfs & Gdl & Gkc & Gkr & Gfz
                        & F64 & F64' & F32 & Gret2 & Gret & Gtp0 & Gtp1 & Gtp2 & Gpr0 & Gpr1 & Ger0 & Ger1 & Gkcs & Ggsh & Gprs & Gtsd & Gtsd0 & Gtsd1 & Gimg & Gimg0 & Gimg1 & Gimg2 & Gimg3 & Gimg4 & Gimg5).
      pose proof A_PRE as (H1 & H2 & H4 & H10 & H11 & Hn & Hd0 & Hdn & Hd16 & Hdhi & Hsp16 & Hsplo & Hsphi & Hfs4 & Hfslo & Hfshi & Hfsimg
                        & Hdj1 & Hdj2 & Hdj3 & Rd & Rsh & Rshm & Rshw & Wfr & Zsh & Wsh & Rm1 & Rm2 & RZ1 & Rh & Wh & Cssl & Cngc
                        & Zfl & Wfl & Rfr & Wfrm & Rfsh & Wfsh & Ctp & Cdb & Cbeg & Ctsd & Cthr & Rthr
                        & Nctx & Nthr & Db0 & Db1 & Cx0 & Cx1 & Th0 & Th1 & AP1 & AP2 & AP3 & Kc & Kg & Kp & Rpr & Wpr & Rer & Wer).
      destruct P_facts as (Pfr & Pws & Pwc & Pfc & Psh & Pfs & Pdl & Pwr & Ptp & Pfz & Psplo & Psphi & Pnmax & Ppris & Pkc & Pkr & Pfd).
      destruct S_rgn as (s & Es & SHF & ER & SD1 & LO & HI & W). destruct (root_shf_ok_facts _ _ _ SHF) as (K & B & N & B8 & C).
      pose proof usp_range as Usp. pose proof ud_range as Ud.
      fold usp in Hsp16, Hsplo, Hsphi, Hdj1, Hdj2, Wfr, Zsh, Wsh, Rm1, Rm2. fold ud in Hd0, Hdn, Hd16, Hdhi, Hdj1, Hdj3, Rd, Rsh, Rshm, Rshw.
      unfold FContractAsan.shadow in Zsh, Wsh, Rm1, Rm2, RZ1, Rfsh, Wfsh.
      pose proof usp0_div8 as D8U.
      unfold LOWMEM_TOP, HIGHMEM_LO, VA_HI, FContractAsan.F_SPLO, FContractAsan.F_SPHI, FS_LEN in *.
      assert (SF : (usp - fa_frame FA) / 8 = usp / 8 - fa_frame FA / 8).
      { pose proof F64 as F. apply Z.mod_divide in F as [q Hq]; [|clear; lia]. rewrite Hq. replace (usp - q * 64) with (usp + (- (q * 8)) * 8) by (clear; lia).
        rewrite Z.div_add by (clear; lia). replace (q * 64) with ((q * 8) * 8) by (clear; lia). rewrite Z.div_mul by (clear; lia). clear; lia. }
      assert (FR8 : - (fa_frame FA / 8) = (- fa_frame FA) / 8).
      { pose proof F64 as F. apply Z.mod_divide in F as [q Hq]; [|clear; lia]. rewrite Hq. replace (q * 64) with ((q * 8) * 8) by (clear; lia).
        rewrite Z.div_mul by (clear; lia). replace (- (q * 8 * 8)) with ((- (q * 8)) * 8) by (clear; lia). rewrite Z.div_mul by (clear; lia). clear; lia. }
      rewrite SF in Zsh, Wsh, Rm1, RZ1.
      assert (U8 : 17591917604864 <= usp / 8 <= 17592186044414) by (split; [apply Z.div_le_lower_bound|apply Z.div_le_upper_bound]; clear - Hsplo Hsphi; lia).
      assert (D8 : 2 <= ud / 8 <= 2305843009213693951) by (split; [apply Z.div_le_lower_bound|apply Z.div_le_upper_bound]; clear - Hd0 Hd16 Hdn Hn Ud; liae).
      assert (R8 : 8 <= fa_frame FA / 8 <= 536870912) by (split; [apply Z.div_le_lower_bound|apply Z.div_le_upper_bound]; clear - F64' F32; lia).
      (* [comment removed for export] *)
      set (z1 := mkFZ SP8 (fa_shoff FA) (lconst (- (fa_frame FA / 8))) (lconst 0) true).
      set (z2 := mkFZ SP8 (fa_shoff FA) (lconst (- (fa_frame FA / 8) - 8)) (lconst (- (fa_frame FA / 8))) false).
      set (z3 := mkFZ SP8 (fa_shoff FA) (lconst 0) (lconst 8) false).
      set (z4 := mkFZ FSB 0 (lconst 0) (lconst FS_HINTS) true).
      assert (IN1 : In z1 (vp_fzones P)) by (rewrite Pfz; left; reflexivity).
      assert (IN2 : In z2 (vp_fzones P)) by (rewrite Pfz; right; left; reflexivity).
      assert (IN3 : In z3 (vp_fzones P)) by (rewrite Pfz; right; right; left; reflexivity).
      assert (IN4 : In z4 (vp_fzones P)) by (rewrite Pfz; do 3 right; left; reflexivity).
      assert (N8 : nuE E2 SP8 = usp / 8) by reflexivity. assert (NF : nuE E2 FSB = fs) by reflexivity.
      assert (ZL1 : zone_lo E2 z1 = fa_shoff FA + usp / 8 - fa_frame FA / 8 /\ zone_hi E2 z1 = fa_shoff FA + usp / 8)
        by (unfold zone_lo, zone_hi; cbn [z1 fz_disp fz_base fz_lo fz_hi]; rewrite N8, !eval_lconst; clear; lia).
      assert (ZL2 : zone_lo E2 z2 = fa_shoff FA + usp / 8 - fa_frame FA / 8 - 8 /\ zone_hi E2 z2 = fa_shoff FA + usp / 8 - fa_frame FA / 8)
        by (unfold zone_lo, zone_hi; cbn [z2 fz_disp fz_base fz_lo fz_hi]; rewrite N8, !eval_lconst; clear; lia).
      assert (ZL3 : zone_lo E2 z3 = fa_shoff FA + usp / 8 /\ zone_hi E2 z3 = fa_shoff FA + usp / 8 + 8)
        by (unfold zone_lo, zone_hi; cbn [z3 fz_disp fz_base fz_lo fz_hi]; rewrite N8, !eval_lconst; clear; lia).
      assert (ZL4 : zone_lo E2 z4 = fs /\ zone_hi E2 z4 = fs + 88)
        by (unfold zone_lo, zone_hi; cbn [z4 fz_disp fz_base fz_lo fz_hi]; rewrite NF, !eval_lconst; unfold FS_HINTS; clear; lia).
      rewrite ER. intros [<-|[<-|[<-|[]]]].
      - (* [comment removed for export] *)
        assert (RB : rbase nu (vregion_of s) = fa_shoff FA + usp / 8).
        { unfold rbase. cbn [vregion_of vr_disp vr_base]. rewrite SD1, B, Psh. reflexivity. }
        unfold region_ok, region_cells_ok, region_perm_ok, region_nul_ok. rewrite RB.
        cbn [vregion_of vr_lo vr_hi vr_kind vr_cells vr_w vr_nul vr_disp vr_base vr_b8]. rewrite LO, HI, W, N. unfold is_data_shadow, is_shadow. cbn [vregion_of vr_kind]. rewrite K. cbn [rkind_of].
        split; [clear - U8 R8 Gsh'; lia|]. split; [clear - U8 Gsh'; lia|]. split; [clear - R8; lia|].
        split; [intros X; discriminate|].
        split.
        { intros off w v Hin. apply vregion_of_cells in Hin as (e & -> & Hin). destruct (C _ _ _ Hin) as (C1 & C2 & C3 & ->).
          split; [clear - C1 R8; lia|]. split; [exact C2|]. split; [clear - C3 D8U; lia|].
          cbn [rcell_holds lin_is_const lconst lt lc andb is_nilb]. intros i Hi.
          destruct (zeroes_at SEGS _ _ _ (fa_shoff FA + usp / 8 + off + i) Zsh ltac:(clear - Hi C1 C3 D8U; lia)) as (b & Hb & Hb0).
          exists b. split; [exact Hb|rewrite Hb0; reflexivity]. }
        split.
        { intros _. split.
          - intros off Hoff. split.
            + destruct (Z.lt_ge_cases off (- (fa_frame FA / 8))) as [X|X]; [apply (in_any_zone_intro z2 _ IN2); clear - ZL2 Hoff X; lia|].
              destruct (Z.lt_ge_cases off 0) as [Y|Y]; [apply (in_any_zone_intro z1 _ IN1); clear - ZL1 X Y; lia|].
              apply (in_any_zone_intro z3 _ IN3); clear - ZL3 Hoff Y; lia.
            + destruct (Z.lt_ge_cases off (- (fa_frame FA / 8))) as [X|X]; [eapply readable_at; [exact Rm1|clear - Hoff X; lia]|].
              destruct (Z.lt_ge_cases off 0) as [Y|Y]; [eapply readable_at; [exact RZ1|clear - X Y; lia]|].
              eapply readable_at; [exact Rm2|clear - Hoff Y; lia].
          - intros lo hi off [Elh|[]] Hoff. injection Elh as <- <-. rewrite <- FR8 in Hoff.
            split; [clear - Hoff R8 D8U; lia|]. split; [apply (in_rw_zones_intro z1 _ IN1 eq_refl); clear - ZL1 Hoff D8U; lia|].
            split; [eapply writable_at; [exact Wsh|clear - Hoff D8U; lia]|].
            apply (covered_wordZ _ (fa_shoff FA + usp / 8 - fa_frame FA / 8) (fa_frame FA / 8 + u_sp (u1 U) / 8));
              [|clear - U8 R8 Gsh'; lia|clear - Hoff D8U; lia|clear - Hoff D8U; lia|clear - U8 Gsh' Hoff D8U; lia].
            apply (in_unit_regions2_shadow P E2 _ _ Pfs). unfold stack_shadow_regions. rewrite Pws, Psh. cbn [map fst snd ev1 E2 rootE2 rootE e_sp0]. left.
            fold usp. replace (usp + - fa_frame FA) with (usp - fa_frame FA) by (clear; lia). rewrite SF.
            replace ((u_sp (u1 U) - - fa_frame FA) / 8) with (fa_frame FA / 8 + u_sp (u1 U) / 8).
            2:{ destruct usp0_cases as [E|E]; rewrite E; [f_equal; clear; liae|].
                replace (-16 - - fa_frame FA) with (fa_frame FA + (-2) * 8) by (clear; lia). rewrite Z.div_add by (clear; lia). reflexivity. }
            replace (fa_shoff FA + (usp / 8 - fa_frame FA / 8)) with (fa_shoff FA + usp / 8 - fa_frame FA / 8) by (clear; lia). reflexivity. }
        split; [intros lo hi []|].
        (* [comment removed for export] *)
        unfold kind_ok. cbn [vregion_of vr_kind vr_disp vr_base vr_lo vr_hi]. rewrite K. cbn [rkind_of]. rewrite Pfr.
        split; [rewrite Pfs; discriminate|]. split; [exact SD1|]. split; [intros _; rewrite B, LO, HI; split; [reflexivity|clear; lia]|].
        split; [intros X; discriminate|]. split; [intros X; discriminate|]. intros X _ _. exfalso. exact (X eq_refl).
      - (* [comment removed for export] *)
        assert (RB : rbase nu (SHD P) = fa_shoff FA + ud / 8) by (unfold rbase; cbn [SHD vr_disp vr_base]; rewrite Psh; reflexivity).
        unfold region_ok, region_cells_ok, region_perm_ok, region_nul_ok. rewrite RB. cbn [SHD vr_lo vr_hi vr_cells vr_w vr_nul vr_kind vr_disp vr_base].
        unfold is_data_shadow. cbn [SHD vr_kind]. rewrite Pos.eqb_refl.
        split; [clear - D8 Gsh'; lia|]. split; [clear - D8 Gsh'; lia|]. split; [clear; lia|]. split; [auto|].
        split; [intros ? ? ? []|]. split; [intros X; discriminate|]. split; [intros ? ? []|].
        unfold kind_ok. cbn [SHD vr_kind vr_disp vr_base]. split; [rewrite Pfs; discriminate|]. split; [reflexivity|].
        split; [intros X; discriminate|]. split; [reflexivity|]. split; [intros X; discriminate|]. intros _ X _. exfalso. exact (X eq_refl).
      - (* [comment removed for export] *)
        assert (RB : rbase nu FSR = fs) by (unfold rbase; cbn [FSR vr_disp vr_base]; change (nu FSB) with fs; clear; lia).
        unfold region_ok, region_cells_ok, region_perm_ok, region_nul_ok. rewrite RB. cbn [FSR vr_lo vr_hi vr_cells vr_w vr_nul vr_kind vr_disp vr_base].
        unfold is_data_shadow, is_shadow. cbn [FSR vr_kind].
        split; [pose proof fs_nonneg as FS0; clear - Hfslo FS0; lia|]. split; [clear - Hfshi; lia|]. split; [clear; lia|]. split; [intros X; discriminate|].
        split; [intros ? ? ? []|]. split.
        { intros _. split.
          - intros off Hoff. split; [apply (in_any_zone_intro z4 _ IN4); clear - ZL4 Hoff; lia|]. eapply readable_at; [exact Rh|unfold FS_HINTS; clear - Hoff; lia].
          - intros lo hi off [Elh|[]] Hoff. injection Elh as <- <-. split; [exact Hoff|].
            split; [apply (in_rw_zones_intro z4 _ IN4 eq_refl); clear - ZL4 Hoff; lia|].
            split; [eapply writable_at; [exact Wh|unfold FS_HINTS; clear - Hoff; lia]|].
            apply (covered_wordZ _ fs 88); [|pose proof fs_nonneg as FS0; clear - Hfslo FS0; lia|clear - Hoff; lia|clear - Hoff; lia|clear - Hfshi Hoff; lia].
            apply in_unit_regions2_fs. unfold fs_regions. rewrite Pfs. left. reflexivity. }
        split; [intros ? ? []|].
        unfold kind_ok. cbn [FSR vr_kind vr_base vr_disp vr_lo vr_hi]. split; [rewrite Pfs; discriminate|]. repeat split; reflexivity.
    Qed.
    (* [comment removed for export] *)
    #[using="GOK WR SEGHI RU STATIC cls res FP sp ctx thr db PRE Hcls Hres Hanc usp ud"] Theorem root_entry_gamma2 : gamma2 SEGS P E2 mem S nu regs mem.
    Proof.
      pose proof GOK as (Gfr & Gtp & Gtp' & Gerr & Gfc & Gnmax & Gsplo & Gsphi & Gsphi' & Gpris & Gsh & Gsh' & Gfs & Gdl & Gkc & Gkr & Gfz
                        & F64 & F64' & F32 & Gret2 & Gret & Gtp0 & Gtp1 & Gtp2 & Gpr0 & Gpr1 & Ger0 & Ger1 & Gkcs & Ggsh & Gprs & Gtsd & Gtsd0 & Gtsd1 & Gimg & Gimg0 & Gimg1 & Gimg2 & Gimg3 & Gimg4 & Gimg5).
      pose proof A_PRE as (H1 & H2 & H4 & H10 & H11 & Hn & Hd0 & Hdn & Hd16 & Hdhi & Hsp16 & Hsplo & Hsphi & Hfs4 & Hfslo & Hfshi & Hfsimg
                        & Hdj1 & Hdj2 & Hdj3 & Rd & Rsh & Rshm & Rshw & Wfr & Zsh & Wsh & Rm1 & Rm2 & RZ1 & Rh & Wh & Cssl & Cngc
                        & Zfl & Wfl & Rfr & Wfrm & Rfsh & Wfsh & Ctp & Cdb & Cbeg & Ctsd & Cthr & Rthr
                        & Nctx & Nthr & Db0 & Db1 & Cx0 & Cx1 & Th0 & Th1 & AP1 & AP2 & AP3 & Kc & Kg & Kp & Rpr & Wpr & Rer & Wer).
      destruct P_facts as (Pfr & Pws & Pwc & Pfc & Psh & Pfs & Pdl & Pwr & Ptp & Pfz & Psplo & Psphi & Pnmax & Ppris & Pkc & Pkr & Pfd).
      destruct (root_ok2_facts _ _ RU) as (Rroot & Rentry & Rsp & Rws & Rwg & _ & Rcls & Rpre & Rex).
      destruct (root_pre_ok2_facts _ _ _ _ Rpre) as (Pregs & Psl & Pgl & Pnul & Pvs & Pcd & Pmd & Ple & Plv & Pdd & _).
      destruct S_rgn as (s & Es & SHF & ER & SD1 & LO & HI & W). destruct (root_shf_ok_facts _ _ _ SHF) as (K & B & N & B8 & C).
      unfold LOWMEM_TOP, HIGHMEM_LO, VA_HI, FContractAsan.F_SPLO, FContractAsan.F_SPHI, FS_LEN in *.
      assert (STATIC' := STATIC). unfold unit_static_ok2 in STATIC'.
      destruct (cstate2_ok P (u2_pre U) && cstate2_iface_b (u2_pre U) && wrgn_ok U (u2_pre U)) eqn:C0; [|discriminate].
      apply andb_prop in C0 as [C0 _]. apply andb_prop in C0 as [C0 _].
      destruct (load_cstate2_v1_facts P (u2_pre U) (u_entry (u1 U)) [] C0) as (_ & _ & _ & J0).
      split; [exact v1E|]. split; [exact envE|]. split; [exact mcE|]. split; [exact (rootnu2_fix E2)|].
      split.
      { (* [comment removed for export] *) intros q x m Hg. unfold S, load_cstate2 in Hg. cbn [vs_divdef] in Hg. rewrite Pdd in Hg. cbn in Hg. discriminate. }
      split; [exact rgnE|].
      split.
      { (* [comment removed for export] *)
        unfold live_ok. unfold S, load_cstate2. cbn [vs_live vs_rgn]. fold S. rewrite Plv.
        change (load_regions P (cs_rgn (u2_pre U))) with (vs_rgn S). rewrite ER.
        split. { intros s0. split; [intros []|]. intros (r & [<-|[<-|[<-|[]]]] & _ & KF); cbn [vregion_of vr_kind SHD FSR] in KF; [rewrite K in KF; cbn in KF|..]; destruct KF. }
        split; [constructor|]. split.
        { intros r1 r2 [<-|[<-|[<-|[]]]] _; cbn [vregion_of vr_kind SHD FSR]; [rewrite K; cbn [rkind_of]| |]; exact I. }
        cbn [map vr_base vregion_of SHD FSR]. rewrite B. repeat constructor; cbn; intuition discriminate. }
      split.
      { (* [comment removed for export] *)
        unfold state_below2. change (vs_next (v1 S)) with (cs_next (c1 (u2_pre U))). rewrite ER.
        unfold S, load_cstate2. cbn [vs_live vs_divdef vs_memo]. rewrite Plv, Pdd.
        split; [unfold LAST_FIXED2, FIRST_FRESH2 in *; clear - J0; lia|]. split.
        { intros r [<-|[<-|[<-|[]]]]; cbn [vregion_of vr_base vr_cells vr_kind SHD FSR]; rewrite ?B, ?K; cbn [rkind_of].
          - split; [unfold SP8, FIRST_FRESH2 in *; clear - J0; lia|]. split; [|exact I].
            intros k w e Hin. apply (vregion_of_cells s) in Hin as (e' & E' & Hin). injection E' as <-. destruct (C _ _ _ Hin) as (_ & _ & _ & ->). reflexivity.
          - split; [unfold DATA8, FIRST_FRESH2 in *; clear - J0; lia|]. split; [intros ? ? ? []|exact I].
          - split; [unfold FSB, FIRST_FRESH2 in *; clear - J0; lia|]. split; [intros ? ? ? []|exact I]. }
        split; [intros ? []|]. split; [intros q x m Hg; cbn in Hg; discriminate|]. intros ? ? ? []. }
      split.
      { (* [comment removed for export] *) intros _ a w v Hin. unfold S, load_cstate2 in Hin. cbn [v1 vs_globs load_cstate] in Hin. rewrite Pgl in Hin. destruct Hin. }
      split.
      { (* [comment removed for export] *)
        intros _ c p Hc Hp _ _. unfold E2, rootE2. cbn [e_fs].
        pose proof (flag_addr_range fs c p Hc Hp) as FR. unfold VGamma2.FS_FLAGS, VGamma2.FS_FRAMES in FR.
        destruct (zeroes_at SEGS _ _ _ (flag_addr fs c p) Zfl) as (b & Hb & Hb0).
        { unfold FContractAsan.FS_FLAGS, FS_FLAGS_LEN. clear - FR. lia. }
        exists b. split; [|exact Hb0]. rewrite rdn_1 in Hb.
        destruct (mem (wordZ (flag_addr fs c p))) as [b'|] eqn:Em; [injection Hb as ->; reflexivity|].
        rewrite SEGHI in Hb; [discriminate|].
        rewrite u_wordZ; [clear - FR Hfslo Hfsimg Gimg0; lia | clear - FR Hfslo Hfshi Hfsimg Gimg0; lia]. }
      (* [comment removed for export] *)
      intros ? ? ? [].
    Qed.
  End Entry.

  (* [comment removed for export] *)
  Section Exit.
    Variables (regs : bvmap 5 word) (mem : word -> option byte) (sp spa data : word) (n fs ctx thr db : Z).
    Hypothesis PRE : FA_PRE SEGS FA regs mem sp data n fs ctx thr db.
    Hypothesis Hanc : bv_unsigned spa = bv_unsigned sp - u_sp (u1 U).
    Let E2 := rootE2 FA regs spa data n fs.
    Let nu := rootnu2 E2.
    Let usp := bv_unsigned spa.      (* [comment removed for export] *)
    Let usr := bv_unsigned sp.       (* [comment removed for export] *)

    Variables (regs' : bvmap 5 word) (mem' : word -> option byte) (X : cstate2) (nu' : val) (pc : Z) (ctx' : list Z).
    Hypothesis XIN : In X (u2_exits U).
    Hypothesis XG : gamma2 SEGS P E2 mem (load_cstate2 P X pc ctx') nu' regs' mem'.
    Hypothesis XREGS : exit_regs2 G U nu regs'.
    Hypothesis XRA : getr regs' (Z_to_bv 5 1) = wordZ (fa_ret FA).
    Hypothesis XFM : frame_mod mem mem' (unit_regions2 P E2).
    Hypothesis XFL : forall a, in_flags_zone P E2 a -> mem' (wordZ a) = mem (wordZ a).

    (* [comment removed for export] *)
    #[using="SEGS GOK RU res mem ctx thr db PRE Hanc usp"] Lemma unit_regions2_in_FA a : outside a (FA_footprint FA usr fs) -> outside a (unit_regions2 P E2).
    Proof.
      pose proof GOK as (Gfr & Gtp & Gtp' & Gerr & Gfc & Gnmax & Gsplo & Gsphi & Gsphi' & Gpris & Gsh & Gsh' & Gfs & Gdl & Gkc & Gkr & Gfz
                        & F64 & F64' & F32 & Gret2 & Gret & Gtp0 & Gtp1 & Gtp2 & Gpr0 & Gpr1 & Ger0 & Ger1 & Gkcs & Ggsh & Gprs & Gtsd & Gtsd0 & Gtsd1 & Gimg & Gimg0 & Gimg1 & Gimg2 & Gimg3 & Gimg4 & Gimg5).
      pose proof PRE as (H1 & H2 & H4 & H10 & H11 & Hn & Hd0 & Hdn & Hd16 & Hdhi & Hsp16 & Hsplo & Hsphi & Hfs4 & Hfslo & Hfshi & Hfsimg & _).
      destruct P_facts as (Pfr & Pws & Pwc & Pfc & Psh & Pfs & Pdl & Pwr & Ptp & Pfz & Psplo & Psphi & Pnmax & Ppris & Pkc & Pkr & Pfd).
      fold usr in Hsp16, Hsplo, Hsphi. unfold LOWMEM_TOP, HIGHMEM_LO, VA_HI, FContractAsan.F_SPLO, FContractAsan.F_SPHI, FS_LEN in *.
      pose proof (u_word_lt sp) as Usp. fold usr in Usp.
      assert (AN : usp = usr - u_sp (u1 U)) by exact Hanc. pose proof usp0_div8 as D8U.
      assert (AN8 : usp / 8 = usr / 8 - u_sp (u1 U) / 8).
      { rewrite AN. destruct usp0_cases as [E|E]; rewrite E; [f_equal; (ltac2:(LK.k [@Hd0; @Hsp16; @E; @H; @H0; @H7; @H8; @H14; @H15; @H39]); liae)|]. replace (usr - -16) with (usr + 2 * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
      intros OUT. rewrite outside_forall in OUT. apply (proj2 (outside_forall _ _)). intros b m Hin Hrng.
      unfold FA_footprint, FA_writes in OUT. cbn [map fst snd] in OUT. unfold FContractAsan.shadow in OUT.
      assert (SF : forall x, (x - fa_frame FA) / 8 = x / 8 - fa_frame FA / 8).
      { intros x. pose proof F64 as F. apply Z.mod_divide in F as [q Hq]; [|clear; lia]. rewrite Hq. replace (x - q * 64) with (x + (- (q * 8)) * 8) by (clear; lia).
        rewrite Z.div_add by (clear; lia). replace (q * 64) with ((q * 8) * 8) by (clear; lia). rewrite Z.div_mul by (clear; lia). clear; lia. }
      (* [comment removed for export] *)
      assert (SUB : forall x mx x' mx', In (Z_to_bv 64 x', mx') (map (fun r : Z * Z => (Z_to_bv 64 (fst r), snd r)) (FA_writes FA usr fs)) ->
                      0 <= x' -> x' <= x -> x + mx <= x' + mx' -> x + mx <= 2 ^ 64 -> b = wordZ x -> m = mx -> False).
      { intros x mx x' mx' Hin' X0 X1 X2 X3 -> ->. apply (OUT _ _ Hin'). unfold in_rng in Hrng |- *.
        change (Z_to_bv 64 x') with (wordZ x'). rewrite u_wordZ in Hrng |- *; try (clear - X0 X1 X2 X3 Hrng; lia).
        all: destruct (Z.lt_ge_cases 0 mx); [rewrite u_wordZ in Hrng by (clear - X0 X1 X2 X3 H; lia); clear - X0 X1 X2 X3 Hrng; lia | clear - Hrng H; rewrite ?u_wordZ in Hrng; lia]. }
      unfold FA_writes in SUB. cbn [map fst snd] in SUB. unfold FContractAsan.shadow in SUB. rewrite (SF usr) in SUB.
      assert (R8 : 8 <= fa_frame FA / 8 <= 536870912) by (split; [apply Z.div_le_lower_bound|apply Z.div_le_upper_bound]; clear - F64' F32; lia).
      assert (U8 : 17591917604864 <= usr / 8 <= 17592186044414) by (split; [apply Z.div_le_lower_bound|apply Z.div_le_upper_bound]; clear - Hsplo Hsphi; lia).
      unfold unit_regions2 in Hin. rewrite Pfs in Hin. unfold arg_regions in Hin. rewrite Pwr in Hin. cbn [map] in Hin.
      apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [[]|Hin]; apply in_app_iff in Hin as [Hin|Hin]].
      - (* [comment removed for export] *)
        unfold unit_regions in Hin. rewrite Pws in Hin. cbn [map fst snd ev1 E2 rootE2 rootE e_sp0] in Hin. fold usp in Hin.
        destruct Hin as [E0|Hin].
        + injection E0 as <- <-. eapply (SUB (usp + - fa_frame FA) (u_sp (u1 U) - - fa_frame FA) (usr - fa_frame FA) (fa_frame FA)); [left; reflexivity| | | | |f_equal|]; clear - F32 F64' Hsplo Hsphi Usp AN D8U; lia.
        + unfold cells_regions in Hin. apply in_map_iff in Hin as (c & Ec & Hc). injection Ec as Eb Em. subst b m. apply Pwc in Hc. rewrite Pfc in Hc.
          destruct Hc as [<-|[<-|[]]]; cbn [fst snd] in *.
          * eapply (SUB (fa_prng FA) 8 (fa_prng FA) 8); [do 6 right; left; reflexivity| | | | |reflexivity|reflexivity]; clear - Gpr0 Gpr1 Gtp1 Gtsd1; lia.
          * eapply (SUB (fa_errno FA) 4 (fa_errno FA) 4); [do 7 right; left; reflexivity| | | | |reflexivity|reflexivity]; clear - Ger0 Ger1 Gtp1 Gtsd1; lia.
      - (* [comment removed for export] *)
        unfold stack_shadow_regions in Hin. rewrite Pws, Psh in Hin. cbn [map fst snd ev1 E2 rootE2 rootE e_sp0] in Hin. fold usp in Hin.
        destruct Hin as [E0|[]]. injection E0 as Eb Em.
        assert (SF' : (usp + - fa_frame FA) / 8 = usp / 8 - fa_frame FA / 8) by (replace (usp + - fa_frame FA) with (usp - fa_frame FA) by (clear; lia); apply SF).
        assert (M' : (u_sp (u1 U) - - fa_frame FA) / 8 = fa_frame FA / 8 + u_sp (u1 U) / 8).
        { destruct usp0_cases as [E|E]; rewrite E; [f_equal; clear; liae|].
          replace (-16 - - fa_frame FA) with (fa_frame FA + (-2) * 8) by (clear; lia). rewrite Z.div_add by (clear; lia). reflexivity. }
        eapply (SUB (fa_shoff FA + (usp + - fa_frame FA) / 8) ((u_sp (u1 U) - - fa_frame FA) / 8) (fa_shoff FA + (usr / 8 - fa_frame FA / 8)) (fa_frame FA / 8));
          [right; left; reflexivity | clear - R8 U8 Gsh'; lia | rewrite SF', AN8; clear - D8U; lia | rewrite SF', M', AN8; clear - D8U; lia
          | rewrite SF', M', AN8; clear - R8 U8 Gsh' D8U; lia | symmetry; exact Eb | symmetry; exact Em].
      - (* [comment removed for export] *)
        unfold fs_regions in Hin. rewrite Pfs in Hin. cbn [e_fs E2 rootE2 e_live] in Hin.
        apply in_app_iff in Hin as [Hin|Hin].
        + destruct Hin as [E0|[E0|[]]]; injection E0 as <- <-.
          * eapply (SUB fs 88 fs FS_HINTS); [do 2 right; left; reflexivity| | | | |reflexivity|reflexivity]; unfold FS_HINTS; clear - Hfslo Hfshi Hfsimg Gimg0; lia.
          * eapply (SUB (fs + VGamma2.FS_FLAGS) 32768 (fs + FContractAsan.FS_FLAGS) FS_FLAGS_LEN); [do 3 right; left; reflexivity| | | | |reflexivity|reflexivity];
              unfold VGamma2.FS_FLAGS, FContractAsan.FS_FLAGS, FS_FLAGS_LEN; clear - Hfslo Hfshi Hfsimg Gimg0; lia.
        + assert (CL : forall k, In (b, m) (classes_regions P fs k []) -> Z.of_nat k <= 5 ->
                       exists cid pos, 0 <= cid < 5 /\ 0 <= pos < fs_nframes cid /\
                         ((b, m) = (wordZ (frame_addr fs cid pos), fake_size cid)
                          \/ (b, m) = (wordZ (vp_shoff P + frame_addr fs cid pos / 8), fake_size cid / 8))).
          { induction k as [|k IH]; cbn [classes_regions]; intros H Hk; [destruct H|].
            apply in_app_iff in H as [H|H]; [apply IH; [exact H|clear -Hk; lia]|].
            unfold class_regions in H. apply in_flat_map in H as (pos & Hpos & H).
            apply in_map_iff in Hpos as (pn & <- & Hpn). apply in_seq in Hpn.
            destruct (existsb _ _); [destruct H|].
            exists (Z.of_nat k), (Z.of_nat pn). split; [clear -Hk; lia|]. split; [clear -Hpn; lia|].
            destruct H as [E0|[E0|[]]]; [left|right]; symmetry; exact E0. }
          assert (K5 : Z.of_nat (Z.to_nat FS_NCLASSES) <= 5) by (unfold FS_NCLASSES; rewrite Z2Nat.id by (clear; lia); clear; lia).
          destruct (CL _ Hin K5) as (cid & pos & Hc & Hp & CASES).
          pose proof (frame_in_class fs cid pos ltac:(clear -Hc; lia) ltac:(clear -Hc; lia) Hp) as [F1 F2].
          pose proof (fake_size_bounds cid ltac:(clear -Hc; lia)) as FB. unfold VGamma2.FS_FRAMES in F1, F2.
          assert (SFS : (fs + 36864) / 8 = fs / 8 + 4608).
          { replace (fs + 36864) with (fs + 4608 * 8) by (clear; lia). rewrite Z.div_add by (clear; lia). clear; lia. }
          destruct CASES as [E0|E0]; injection E0 as Eb Em.
          * eapply (SUB (frame_addr fs cid pos) (fake_size cid) (fs + FContractAsan.FS_FRAMES) FS_FRAMES_LEN); [do 4 right; left; reflexivity| | | | |exact Eb|exact Em];
              unfold FContractAsan.FS_FRAMES, FS_FRAMES_LEN; clear - F1 F2 FB Hc Hfslo Hfshi Hfsimg Gimg0; lia.
          * assert (A3 : (fs + 36864 + cid * 2 ^ 20) / 8 <= frame_addr fs cid pos / 8) by (apply Z.div_le_mono; [clear; lia|exact F1]).
            assert (A4 : (frame_addr fs cid pos + fake_size cid) / 8 <= (fs + 36864 + (cid + 1) * 2 ^ 20) / 8) by (apply Z.div_le_mono; [clear; lia|exact F2]).
            pose proof (fake_size_mod64 cid ltac:(clear -Hc; lia)) as M64.
            assert (A5 : (frame_addr fs cid pos + fake_size cid) / 8 = frame_addr fs cid pos / 8 + fake_size cid / 8).
            { apply Z.mod_divide in M64 as [q Hq]; [|clear; lia]. rewrite Hq. replace (q * 64) with ((q * 8) * 8) by (clear; lia).
              rewrite Z.div_add, Z.div_mul by (clear; lia). reflexivity. }
            rewrite A5 in A4.
            replace (fs + 36864 + cid * 2 ^ 20) with (fs + (4608 + cid * 131072) * 8) in A3 by (clear; lia). rewrite Z.div_add in A3 by (clear; lia).
            replace (fs + 36864 + (cid + 1) * 2 ^ 20) with (fs + (4608 + (cid + 1) * 131072) * 8) in A4 by (clear; lia). rewrite Z.div_add in A4 by (clear; lia).
            assert (F8 : 0 <= fs / 8 <= 17592186044416) by (split; [apply Z.div_pos|apply Z.div_le_upper_bound]; clear - Hfslo Hfshi Hfsimg Gimg0; lia).
            assert (FB8 : 0 <= fake_size cid / 8) by (apply Z.div_pos; clear - FB; lia).
            eapply (SUB (vp_shoff P + frame_addr fs cid pos / 8) (fake_size cid / 8) (fa_shoff FA + (fs + FContractAsan.FS_FRAMES) / 8) (FS_FRAMES_LEN / 8));
              [do 5 right; left; reflexivity| | | | |exact Eb|exact Em]; unfold FContractAsan.FS_FRAMES, FS_FRAMES_LEN; rewrite ?SFS, ?Psh; clear - A3 A4 F8 FB8 Hc Gsh'; liae.
    Qed.

    (* [comment removed for export] *)
    #[using="SEGS GOK RU res mem ctx thr db PRE Hanc usp"] Lemma bottom_out i : 0 <= i < (- u_sp (u1 U)) / 8 ->
      outside (wordZ (fa_shoff FA + (usr / 8 - fa_frame FA / 8) + i)) (unit_regions2 P E2).
    Proof.
      pose proof GOK as (Gfr & Gtp & Gtp' & Gerr & Gfc & Gnmax & Gsplo & Gsphi & Gsphi' & Gpris & Gsh & Gsh' & Gfs & Gdl & Gkc & Gkr & Gfz
                        & F64 & F64' & F32 & Gret2 & Gret & Gtp0 & Gtp1 & Gtp2 & Gpr0 & Gpr1 & Ger0 & Ger1 & Gkcs & Ggsh & Gprs & Gtsd & Gtsd0 & Gtsd1 & Gimg & Gimg0 & Gimg1 & Gimg2 & Gimg3 & Gimg4 & Gimg5).
      pose proof PRE as (H1 & H2 & H4 & H10 & H11 & Hn & Hd0 & Hdn & Hd16 & Hdhi & Hsp16 & Hsplo & Hsphi & Hfs4 & Hfslo & Hfshi & Hfsimg & Hdj1 & Hdj2 & _).
      destruct P_facts as (Pfr & Pws & Pwc & Pfc & Psh & Pfs & Pdl & Pwr & Ptp & Pfz & Psplo & Psphi & Pnmax & Ppris & Pkc & Pkr & Pfd).
      fold usr in Hsp16, Hsplo, Hsphi, Hdj2. unfold LOWMEM_TOP, HIGHMEM_LO, VA_HI, FContractAsan.F_SPLO, FContractAsan.F_SPHI, FS_LEN in *.
      pose proof (u_word_lt sp) as Usp. fold usr in Usp.
      assert (AN : usp = usr - u_sp (u1 U)) by exact Hanc. pose proof usp0_div8 as D8U.
      assert (AN8 : usp / 8 = usr / 8 - u_sp (u1 U) / 8).
      { rewrite AN. destruct usp0_cases as [E|E]; rewrite E; [f_equal; (ltac2:(LK.k [@H61; @Hd0; @Hd16; @Hsp16; @Hsplo; @E; @H; @H0; @H7; @H8; @H14; @H15; @H39; @H44]); liae)|]. replace (usr - -16) with (usr + 2 * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
      assert (SF : forall x, (x - fa_frame FA) / 8 = x / 8 - fa_frame FA / 8).
      { intros x. pose proof F64 as F. apply Z.mod_divide in F as [q Hq]; [|clear; lia]. rewrite Hq. replace (x - q * 64) with (x + (- (q * 8)) * 8) by (clear; lia).
        rewrite Z.div_add by (clear; lia). replace (q * 64) with ((q * 8) * 8) by (clear; lia). rewrite Z.div_mul by (clear; lia). clear; lia. }
      assert (R8 : 8 <= fa_frame FA / 8 <= 536870912) by (split; [apply Z.div_le_lower_bound|apply Z.div_le_upper_bound]; clear - F64' F32; lia).
      assert (U8 : 17591917604864 <= usr / 8 <= 17592186044414) by (split; [apply Z.div_le_lower_bound|apply Z.div_le_upper_bound]; clear - Hsplo Hsphi; lia).
      assert (FS0 : 0 <= fs) by (clear - Gimg0 Hfsimg; lia).
      intros Hi. set (a := fa_shoff FA + (usr / 8 - fa_frame FA / 8) + i).
      assert (AB : 0x7fff7000 < a < 0x10007fff8000) by (unfold a; rewrite Gsh'; clear - R8 U8 Hi D8U; lia).
      apply (proj2 (outside_forall _ _)). intros b m Hin Hrng.
      (* [comment removed for export] *)
      assert (NOT : forall x mx, b = wordZ x -> m = mx -> 0 <= x -> x + mx <= 2 ^ 64 -> (a < x \/ x + mx <= a) -> False).
      { intros x mx -> -> X0 X1 X2. unfold in_rng in Hrng. destruct (Z.lt_ge_cases 0 mx) as [M|M].
        - rewrite !u_wordZ in Hrng by (clear - AB X0 X1 M; lia). clear - Hrng X2. lia.
        - clear - Hrng M. lia. }
      unfold unit_regions2 in Hin. rewrite Pfs in Hin. unfold arg_regions in Hin. rewrite Pwr in Hin. cbn [map] in Hin.
      apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [[]|Hin]; apply in_app_iff in Hin as [Hin|Hin]].
      - (* [comment removed for export] *)
        unfold unit_regions in Hin. rewrite Pws in Hin. cbn [map fst snd ev1 E2 rootE2 rootE e_sp0] in Hin. fold usp in Hin.
        destruct Hin as [E0|Hin].
        + injection E0 as Eb Em. apply (NOT (usp + - fa_frame FA) (u_sp (u1 U) - - fa_frame FA)); [symmetry; exact Eb|symmetry; exact Em| | |];
            clear - AB AN D8U F32 F64' Hsplo Hsphi Usp; lia.
        + unfold cells_regions in Hin. apply in_map_iff in Hin as (c & Ec & Hc). injection Ec as Eb Em. apply Pwc in Hc. rewrite Pfc in Hc.
          destruct Hc as [<-|[<-|[]]]; cbn [fst snd] in *.
          * apply (NOT (fa_prng FA) 8); [symmetry; exact Eb|symmetry; exact Em| | |]; clear - AB Gpr0 Gpr1 Gtp1 Gtsd1 Gimg1 Gimg5; lia.
          * apply (NOT (fa_errno FA) 4); [symmetry; exact Eb|symmetry; exact Em| | |]; clear - AB Ger0 Ger1 Gtp1 Gtsd1 Gimg1 Gimg5; lia.
      - (* [comment removed for export] *)
        unfold stack_shadow_regions in Hin. rewrite Pws, Psh in Hin. cbn [map fst snd ev1 E2 rootE2 rootE e_sp0] in Hin. fold usp in Hin.
        destruct Hin as [E0|[]]. injection E0 as Eb Em.
        assert (SF' : (usp + - fa_frame FA) / 8 = usp / 8 - fa_frame FA / 8) by (replace (usp + - fa_frame FA) with (usp - fa_frame FA) by (clear; lia); apply SF).
        assert (M' : (u_sp (u1 U) - - fa_frame FA) / 8 = fa_frame FA / 8 + u_sp (u1 U) / 8).
        { destruct usp0_cases as [E|E]; rewrite E; [f_equal; clear; liae|].
          replace (-16 - - fa_frame FA) with (fa_frame FA + (-2) * 8) by (clear; lia). rewrite Z.div_add by (clear; lia). reflexivity. }
        apply (NOT (fa_shoff FA + (usp + - fa_frame FA) / 8) ((u_sp (u1 U) - - fa_frame FA) / 8)); [symmetry; exact Eb|symmetry; exact Em| | |];
          rewrite ?SF', ?M', ?AN8; unfold a; rewrite ?Gsh'; clear - R8 U8 Hi D8U; lia.
      - (* [comment removed for export] *)
        unfold fs_regions in Hin. rewrite Pfs in Hin. cbn [e_fs E2 rootE2 e_live] in Hin.
        apply in_app_iff in Hin as [Hin|Hin].
        + destruct Hin as [E0|[E0|[]]]; injection E0 as Eb Em.
          * apply (NOT fs 88); [symmetry; exact Eb|symmetry; exact Em| | |]; clear - AB Hfslo Hfshi FS0; lia.
          * apply (NOT (fs + VGamma2.FS_FLAGS) 32768); [symmetry; exact Eb|symmetry; exact Em| | |]; unfold VGamma2.FS_FLAGS; clear - AB Hfslo Hfshi FS0; lia.
        + assert (CL : forall k, In (b, m) (classes_regions P fs k []) -> Z.of_nat k <= 5 ->
                       exists cid pos, 0 <= cid < 5 /\ 0 <= pos < fs_nframes cid /\
                         ((b, m) = (wordZ (frame_addr fs cid pos), fake_size cid)
                          \/ (b, m) = (wordZ (vp_shoff P + frame_addr fs cid pos / 8), fake_size cid / 8))).
          { induction k as [|k IH]; cbn [classes_regions]; intros H Hk; [destruct H|].
            apply in_app_iff in H as [H|H]; [apply IH; [exact H|clear -Hk; lia]|].
            unfold class_regions in H. apply in_flat_map in H as (pos & Hpos & H).
            apply in_map_iff in Hpos as (pn & <- & Hpn). apply in_seq in Hpn.
            destruct (existsb _ _); [destruct H|].
            exists (Z.of_nat k), (Z.of_nat pn). split; [clear -Hk; lia|]. split; [clear -Hpn; lia|].
            destruct H as [E0|[E0|[]]]; [left|right]; symmetry; exact E0. }
          assert (K5 : Z.of_nat (Z.to_nat FS_NCLASSES) <= 5) by (unfold FS_NCLASSES; rewrite Z2Nat.id by (clear; lia); clear; lia).
          destruct (CL _ Hin K5) as (cid & pos & Hc & Hp & CASES).
          pose proof (frame_in_class fs cid pos ltac:(clear -Hc; lia) ltac:(clear -Hc; lia) Hp) as [F1 F2].
          pose proof (fake_size_bounds cid ltac:(clear -Hc; lia)) as FB. unfold VGamma2.FS_FRAMES in F1, F2.
          destruct CASES as [E0|E0]; injection E0 as Eb Em.
          * apply (NOT (frame_addr fs cid pos) (fake_size cid)); [exact Eb|exact Em| | |]; clear - AB F1 F2 FB Hc Hfslo Hfshi FS0; lia.
          * assert (A3 : (fs + 36864 + cid * 2 ^ 20) / 8 <= frame_addr fs cid pos / 8) by (apply Z.div_le_mono; [clear; lia|exact F1]).
            assert (A4 : (frame_addr fs cid pos + fake_size cid) / 8 <= (fs + 36864 + (cid + 1) * 2 ^ 20) / 8) by (apply Z.div_le_mono; [clear; lia|exact F2]).
            pose proof (fake_size_mod64 cid ltac:(clear -Hc; lia)) as M64.
            assert (A5 : (frame_addr fs cid pos + fake_size cid) / 8 = frame_addr fs cid pos / 8 + fake_size cid / 8).
            { apply Z.mod_divide in M64 as [q Hq]; [|clear; lia]. rewrite Hq. replace (q * 64) with ((q * 8) * 8) by (clear; lia).
              rewrite Z.div_add, Z.div_mul by (clear; lia). reflexivity. }
            rewrite A5 in A4.
            replace (fs + 36864 + cid * 2 ^ 20) with (fs + (4608 + cid * 131072) * 8) in A3 by (clear; lia). rewrite Z.div_add in A3 by (clear; lia).
            replace (fs + 36864 + (cid + 1) * 2 ^ 20) with (fs + (4608 + (cid + 1) * 131072) * 8) in A4 by (clear; lia). rewrite Z.div_add in A4 by (clear; lia).
            assert (FB8 : 0 <= fake_size cid / 8) by (apply Z.div_pos; clear - FB; lia).
            assert (FSD : fs / 8 * 8 <= fs) by (pose proof (Z.mul_div_le fs 8 ltac:(lia)); lia).
            assert (SD : usr / 8 * 8 <= usr < usr / 8 * 8 + 8) by (pose proof (Z.mul_div_le usr 8 ltac:((ltac2:(LK.k [@K5; @F64'; @Gret; @Hd0; @Hsplo; @Hfslo; @AN; @D8U; @FS0; @Hc; @F1; @FB; @H; @H0; @H3]); lia))); pose proof (Z.div_mod usr 8 ltac:((ltac2:(LK.k [@K5; @F64'; @Gret; @Hd0; @Hsplo; @Hfslo; @AN; @D8U; @FS0; @Hc; @F1; @FB; @H; @H0; @H3]); lia))); pose proof (Z.mod_pos_bound usr 8 ltac:((ltac2:(LK.k [@K5; @F64'; @Gret; @Hd0; @Hsplo; @Hfslo; @AN; @D8U; @FS0; @Hc; @F1; @FB; @H; @H0; @H3]); lia))); (ltac2:(LK.k [@K5; @F64'; @Gret; @Hd0; @Hsplo; @Hfslo; @AN; @D8U; @FS0; @Hc; @F1; @FB; @H; @H0; @H3]); lia)).
            assert (FSD' : fs < fs / 8 * 8 + 8) by (pose proof (Z.div_mod fs 8 ltac:((ltac2:(LK.k [@K5; @F64'; @Gret; @Hd0; @Hsplo; @Hfslo; @AN; @D8U; @FS0; @Hc; @F1; @FB; @H; @H0]); lia))); pose proof (Z.mod_pos_bound fs 8 ltac:((ltac2:(LK.k [@K5; @F64'; @Gret; @Hd0; @Hsplo; @Hfslo; @AN; @D8U; @FS0; @Hc; @F1; @FB; @H; @H0]); lia))); (ltac2:(LK.k [@K5; @F64'; @Gret; @Hd0; @Hsplo; @Hfslo; @AN; @D8U; @FS0; @Hc; @F1; @FB; @H; @H0]); lia)).
            apply (NOT (vp_shoff P + frame_addr fs cid pos / 8) (fake_size cid / 8)); [exact Eb|exact Em| | |]; rewrite ?Psh;
              unfold a; rewrite ?Gsh'; clear - A3 A4 FB8 Hc Hdj2 Hfslo Hfshi FS0 R8 U8 Hi D8U FSD FSD' SD Gsh'; liae.
    Qed.

    (* [comment removed for export] *)
    #[using="G GOK U RU P res spa data n ctx thr db PRE Hanc E2 nu usp X nu' pc ctx' XIN XG XREGS XRA XFM XFL"] Lemma root_exit_post2 :
      ekeeps regs regs' /\ getr regs' 10%bv = Z_to_bv 64 0
      /\ frame_mod mem mem' (FA_footprint FA usr fs)
      /\ FContractAsan.zeroes SEGS mem' (FContractAsan.shadow FA (usr - fa_frame FA)) (fa_frame FA / 8)
      /\ FContractAsan.zeroes SEGS mem' (fs + FContractAsan.FS_FLAGS) FS_FLAGS_LEN.
    Proof.
      pose proof GOK as (Gfr & Gtp & Gtp' & Gerr & Gfc & Gnmax & Gsplo & Gsphi & Gsphi' & Gpris & Gsh & Gsh' & Gfs & Gdl & Gkc & Gkr & Gfz
                        & F64 & F64' & F32 & Gret2 & Gret & Gtp0 & Gtp1 & Gtp2 & Gpr0 & Gpr1 & Ger0 & Ger1 & Gkcs & Ggsh & Gprs & Gtsd & Gtsd0 & Gtsd1 & Gimg & Gimg0 & Gimg1 & Gimg2 & Gimg3 & Gimg4 & Gimg5).
      pose proof PRE as (H1 & H2 & H4 & H10 & H11 & Hn & Hd0 & Hdn & Hd16 & Hdhi & Hsp16 & Hsplo & Hsphi & Hfs4 & Hfslo & Hfshi & Hfsimg
                        & Hdj1 & Hdj2 & Hdj3 & Rd & Rsh & Rshm & Rshw & Wfr & Ru16 & Zsh & Wsh & Rm1 & Rm2 & Rh & Wh & Cssl & Cngc
                        & Zfl & _).
      destruct P_facts as (Pfr & Pws & Pwc & Pfc & Psh & Pfs & Pdl & Pwr & Ptp & Pfz & Psplo & Psphi & Pnmax & Ppris & Pkc & Pkr & Pfd).
      destruct (root_ok2_facts _ _ RU) as (Rroot & Rentry & Rsp & Rws & Rwg & _ & Rcls & Rpre & Rex).
      fold usr in Hsp16, Hsplo, Hsphi, Zsh. unfold LOWMEM_TOP, HIGHMEM_LO, VA_HI, FContractAsan.F_SPLO, FContractAsan.F_SPHI, FS_LEN in *.
      pose proof (u_word_lt sp) as Usp. fold usr in Usp.
      assert (AN : usp = usr - u_sp (u1 U)) by exact Hanc. pose proof usp0_div8 as D8U.
      assert (AN8 : usp / 8 = usr / 8 - u_sp (u1 U) / 8).
      { rewrite AN. destruct usp0_cases as [E|E]; rewrite E; [f_equal; (ltac2:(LK.k [@F64'; @Gtp1; @Gpr0; @Gpr1; @Gimg1; @H71; @Hd0; @Hd16; @Hsp16; @Hsplo; @Hfslo; @Hfsimg; @Hdj1; @Hdj2; @Hdj3; @E; @H; @H0; @H7; @H8; @H14; @H15; @H49; @H54]); liae)|]. replace (usr - -16) with (usr + 2 * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
      rewrite <- (reg_lit 1%bv 1 eq_refl) in H1. rewrite <- (reg_lit 2%bv 2 eq_refl) in H2. rewrite <- (reg_lit 4%bv 4 eq_refl) in H4.
      pose proof XG as (XV1 & _ & _ & XF2 & _ & XRG & _). pose proof XV1 as (_ & _ & _ & _ & _ & _ & _ & XR & _).
      destruct XREGS as (XR2 & XR3 & XR4 & XRS).
      split; [|split; [|split; [|split]]].
      - (* [comment removed for export] *)
        intros r Hin. unfold ekept in Hin. simpl in Hin.
        assert (K1 : getr regs' (Z_to_bv 5 1) = getr regs (Z_to_bv 5 1)).
        { rewrite XRA, H1. apply word_eq_u. rewrite u_wordZ by (clear - Gret; lia). symmetry. rewrite u_Z_to_bv64. unfold zwrap. apply Z.mod_small. clear - Gret; lia. }
        assert (K2 : getr regs' (Z_to_bv 5 2) = getr regs (Z_to_bv 5 2)).
        { apply word_eq_u. replace (Z_to_bv 5 2) with (2%bv : reg) by (apply bv_eq; reflexivity).
          rewrite XR2. change (nu SP0) with usp. rewrite AN. replace (usr - u_sp (u1 U) + u_sp (u1 U)) with usr by lia.
          replace (2%bv : reg) with (Z_to_bv 5 2) by (apply bv_eq; reflexivity). rewrite H2. apply zwrap64_u. }
        assert (K3 : getr regs' (Z_to_bv 5 3) = getr regs (Z_to_bv 5 3)).
        { apply word_eq_u. replace (Z_to_bv 5 3) with (3%bv : reg) at 1 by (apply bv_eq; reflexivity).
          rewrite XR3. change (nu GP) with (bv_unsigned (getr regs (Z_to_bv 5 3))). apply zwrap64_u. }
        assert (K4 : getr regs' (Z_to_bv 5 4) = getr regs (Z_to_bv 5 4)).
        { apply word_eq_u. replace (Z_to_bv 5 4) with (4%bv : reg) at 1 by (apply bv_eq; reflexivity).
          rewrite XR4, H4, Gtp. symmetry. apply u_Z_to_bv64. }
        assert (KS : forall r i, In (r, i) sreg_idx -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
        { intros r0 i Hri. apply word_eq_u. rewrite (XRS _ _ Hri). unfold nu, E2. rewrite (rootnu2_SREG FA regs spa data n fs _ _ Hri). apply zwrap64_u. }
        clear - Hin K1 K2 K3 K4 KS.
        repeat (destruct Hin as [<-|Hin]); try (destruct Hin).
        all: match goal with |- getr _ ?rr = getr _ _ =>
               let k := eval vm_compute in (bv_unsigned rr) in
               replace rr with (Z_to_bv 5 k) by (apply bv_eq; reflexivity) end.
        all: first [exact K1 | exact K2 | exact K3 | exact K4 | eapply KS; unfold sreg_idx; simpl; tauto].
      - (* [comment removed for export] *)
        specialize (Rex _ XIN). unfold root_exit_ok2 in Rex. apply andb_prop in Rex as [Rex _]. apply andb_prop in Rex as [Rex _].
        unfold root_exit_ok in Rex.
        change (vs_regs (load_cstate (c1 X) 0 [])) with (vs_regs (v1 (load_cstate2 P X pc ctx'))) in Rex.
        destruct (pm_get (reg_key 10) (vs_regs (v1 (load_cstate2 P X pc ctx')))) as [e|] eqn:G10; [|discriminate].
        apply lin_eqb_eq in Rex. subst e.
        apply word_eq_u. replace (10%bv : reg) with (Z_to_bv 5 10) by (apply bv_eq; reflexivity). rewrite (XR (Z_to_bv 5 10) (lconst 0)).
        + rewrite eval_lconst. rewrite u_Z_to_bv64. reflexivity.
        + vm_compute. discriminate.
        + exact G10.
      - (* [comment removed for export] *)
        eapply frame_mod_weaken; [|exact XFM]. exact unit_regions2_in_FA.
      - (* [comment removed for export] *)
        specialize (Rex _ XIN). unfold root_exit_ok2 in Rex. apply andb_prop in Rex as [Rex R3]. apply andb_prop in Rex as [_ R2].
        destruct (cs_rgn X) as [|sx [|]] eqn:EX; try discriminate.
        destruct (sr_kind sx) as [| | |o] eqn:KX; try discriminate.
        apply andb_prop in R3 as [R3 CX]. apply andb_prop in R3 as [OX BX]. apply Pos.eqb_eq in OX. subst o. apply Pos.eqb_eq in BX.
        apply existsb_exists in CX as ([k [w [e|]]] & Hcell & E3); [|discriminate]. apply andb_prop in E3 as [E3 Ee]. apply andb_prop in E3 as [Ek Ew].
        apply Z.eqb_eq in Ek. apply Z.eqb_eq in Ew. apply lin_eqb_eq in Ee. subst k w e.
        (* [comment removed for export] *)
        assert (HR : In (vregion_of sx) (vs_rgn (load_cstate2 P X pc ctx'))).
        { unfold load_cstate2. cbn [vs_rgn]. unfold load_regions. rewrite EX. left. reflexivity. }
        pose proof (XRG _ HR) as (_ & _ & _ & _ & XCELLS & _ & _ & XKIND).
        unfold kind_ok in XKIND. cbn [vregion_of vr_kind] in XKIND. rewrite KX in XKIND. cbn [rkind_of] in XKIND.
        destruct XKIND as (_ & XD & _).
        assert (RB : rbase nu' (vregion_of sx) = fa_shoff FA + usp / 8).
        { unfold rbase. rewrite XD. cbn [vregion_of vr_base]. rewrite BX, Psh. rewrite (XF2 SP8 (usp / 8)) by reflexivity. reflexivity. }
        assert (HC : In (- (fa_frame FA / 8), (fa_frame FA / 8 + u_sp (u1 U) / 8, Some (lconst 0))) (vr_cells (vregion_of sx))) by exact Hcell.
        destruct (XCELLS _ _ _ HC) as (_ & _ & _ & RC). rewrite RB in RC.
        unfold rcell_holds, is_shadow in RC. cbn [vregion_of vr_kind] in RC. rewrite KX in RC. cbn [rkind_of lin_is_const lconst lt is_nilb andb lc] in RC.
        intros i Hi. unfold FContractAsan.shadow.
        assert (SF : (usr - fa_frame FA) / 8 = usr / 8 - fa_frame FA / 8).
        { pose proof F64 as F. apply Z.mod_divide in F as [q Hq]; [|clear; lia]. rewrite Hq. replace (usr - q * 64) with (usr + (- (q * 8)) * 8) by (clear; lia).
          rewrite Z.div_add by (clear; lia). replace (q * 64) with ((q * 8) * 8) by (clear; lia). rewrite Z.div_mul by (clear; lia). clear; lia. }
        rewrite SF.
        destruct (Z.lt_ge_cases i ((- u_sp (u1 U)) / 8)) as [LOW|HIGH].
        + (* [comment removed for export] *)
          unfold FContractAsan.shadow in Zsh. rewrite SF in Zsh.
          rewrite <- wordZ_to_bv. rewrite rdn_1, (proj1 XFM _ (bottom_out i ltac:(clear - Hi LOW; lia))). rewrite <- rdn_1. rewrite wordZ_to_bv. apply Zsh. exact Hi.
        + destruct (RC (i - (- u_sp (u1 U)) / 8) ltac:(clear - Hi HIGH D8U; lia)) as (kb & Hkb & Hk0).
          replace (fa_shoff FA + (usr / 8 - fa_frame FA / 8) + i) with (fa_shoff FA + usp / 8 + - (fa_frame FA / 8) + (i - (- u_sp (u1 U)) / 8)) by (rewrite AN8; clear - D8U; lia).
          rewrite <- wordZ_to_bv. rewrite Hkb. f_equal. f_equal. apply bv_eq. rewrite Hk0. change (Z.land 0 255) with 0. symmetry. apply u_Z_to_bv8. clear; lia.
      - (* [comment removed for export] *)
        intros i Hi. rewrite <- wordZ_to_bv. rewrite rdn_1, XFL.
        + rewrite <- rdn_1. apply Zfl. exact Hi.
        + unfold in_flags_zone. rewrite Pfs. cbn [e_fs E2 rootE2]. unfold VGamma2.FS_FLAGS, FContractAsan.FS_FLAGS, FS_FLAGS_LEN in *. clear - Hi. lia.
    Qed.
  End Exit.
End TopA.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section MainA.
  Variable SEGS : list Segment.
  Variable G : genv2.
  Variable FA : FAParams.
  Hypothesis GOK : fa_genv_prop G FA.
  Hypothesis PO0 : params_ok2 SEGS (ge2_P0 G).
  Hypothesis WR : segs_wr_readable SEGS = true.
  Hypothesis SEGHI : forall a : word, fa_imgend FA <= bv_unsigned a -> seg_rom SEGS a = None.   (* [comment removed for export] *)
  Variable C : vcert2.
  (* [comment removed for export] *)
  Hypothesis UNITS : forall rom U, In U C -> root_ok2 FA U = true -> unit_okS2 SEGS G rom U.
  Hypothesis ROK : roots_ok2 FA C = true.

  #[using="G GOK WR SEGHI C UNITS ROK"] Theorem F_contract_asan_of_roots : F_contract_asan SEGS FA.
  Proof.
    pose proof GOK as (Gfr & Gtp & Gtp' & Gerr & Gfc & Gnmax & Gsplo & Gsphi & Gsphi' & Gpris & Gsh & Gsh' & Gfs & Gdl & Gkc & Gkr & Gfz
                      & F64 & F64' & F32 & Gret2 & Gret & _).
    unfold F_contract_asan.
    intros regs mem rom sp data n fs ctx thr db. cbv zeta.
    intros H1 H2 H4 H10 H11 Hn Hd0 Hdn Hd16 Hdhi Hsp16 Hsplo Hsphi Hfs4 Hfslo Hfshi Hfsimg Hdj1 Hdj2 Hdj3 Rd Rsh Rshm Rshw Wfr Ru16 Zsh Wsh Rm1 Rm2 Rh Wh Cssl Cngc
           Zfl Wfl Rfr Wfrm Rfsh Wfsh Ctp Cdb Cbeg Ctsd Cthr Rthr Nctx Nthr Db0 Db1 Cx0 Cx1 Th0 Th1 AP1 AP2 AP3 Kc Kg Kp Rpr Wpr Rer Wer.
    assert (PRE : FA_PRE SEGS FA regs mem sp data n fs ctx thr db) by (repeat (split; [assumption|]); assumption).
    (* [comment removed for export] *)
    set (res := bv_unsigned sp mod 32).
    assert (RES : res = 0 \/ res = 16).
    { subst res. clear - Hsp16. pose proof (Z.div_mod (bv_unsigned sp) 16 ltac:(lia)) as D16. rewrite Hsp16, Z.add_0_r in D16.
      set (k := bv_unsigned sp / 16) in D16. pose proof (Z.div_mod k 2 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound k 2 ltac:(lia)) as B2.
      rewrite D16. replace (16 * k) with (16 * (k mod 2) + (k / 2) * 32) by lia. rewrite Z_mod_plus_full.
      rewrite Z.mod_small by lia. lia. }
    unfold roots_ok2 in ROK. apply andb_prop in ROK as [ROK0 ROK16].
    assert (ROOT : exists U, In U C /\ root_ok2 FA U = true /\ root_res U = res /\ fst (u_sclass (u1 U)) <= n <= snd (u_sclass (u1 U))).
    { destruct RES as [ER|ER]; rewrite ER.
      - destruct (cover_sound _ _ _ _ ROK0 n) as (c & Hc & Hcn); [lia|].
        apply in_map_iff in Hc as (U & EqC & HU). unfold roots2 in HU. apply filter_In in HU as [HinC RU].
        apply andb_prop in RU as [RU RR]. apply Z.eqb_eq in RR. exists U. rewrite EqC. auto.
      - destruct (cover_sound _ _ _ _ ROK16 n) as (c & Hc & Hcn); [lia|].
        apply in_map_iff in Hc as (U & EqC & HU). unfold roots2 in HU. apply filter_In in HU as [HinC RU].
        apply andb_prop in RU as [RU RR]. apply Z.eqb_eq in RR. exists U. rewrite EqC. auto. }
    destruct ROOT as (U & HinC & RU & RR & Hcls).
    pose proof (root_ok2_facts _ _ RU) as (Rroot & Rentry & Rsp & Rws & Rwg & _ & Rcls & Rpre & Rex).
    destruct (UNITS rom U HinC RU) as [STATIC OK].
    (* [comment removed for export] *)
    set (spa := wordZ (bv_unsigned sp - u_sp (u1 U))).
    assert (Hanc : bv_unsigned spa = bv_unsigned sp - u_sp (u1 U)).
    { unfold spa. pose proof (u_word_lt sp) as Usp. unfold FContractAsan.F_SPHI in Hsphi. apply u_wordZ. destruct Rsp as [E|E]; rewrite E; lia. }
    set (E2 := rootE2 FA regs spa data n fs). set (nu := rootnu2 E2).
    assert (RET : unit_ret2 U E2 = fa_ret FA) by (unfold unit_ret2, unit_ret; now rewrite Rroot).
    pose proof (OK E2 mem nu regs mem) as UOK. rewrite RET, Rentry in UOK.
    destruct UOK as (regs' & mem' & MS & EX).
    { apply ret_ok_even. rewrite u_wordZ; [exact Gret2|exact Gret]. }
    { unfold gammaU2, PU2. rewrite <- Rentry. subst E2 nu.
      eapply (root_entry_gamma2 SEGS G FA GOK); eauto. }
    exists regs', mem'. split; [exact MS|].
    destruct EX as (X & nu' & HX & [HGX _] & EXT & RA1 & XREGS & FMX & FLX).
    rewrite RET in HGX, RA1. unfold gammaU2, PU2, regionsU2 in HGX, FMX. change (PU2 G U) with (unit_params2 G U) in FLX.
    rewrite <- (reg_lit 1%bv 1 eq_refl) in RA1.
    eapply (root_exit_post2 SEGS G FA GOK); eauto.
  Qed.
End MainA.
