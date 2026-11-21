(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (len_rw also unfolds wok_lo and stack_window_reach; new lemmas msteps_run_segments, bwd_run_segments and wbytes_same_m). *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Export
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim
  MemSplit StartupAux ZStores.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Export StoreOkChain.   (* [comment removed for export] *)
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Export RdnChain.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac pin :=
  repeat match goal with
         | H : getr ?rs ?r = _ |- context [getr ?rs ?r] => rewrite !H
         end.

(* [comment removed for export] *)
Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with
             | context [Z_to_bv 64 _] => fail
             | _ => rewrite (u_Z2bv z) by lia
             end
         end.

(* [comment removed for export] *)
Ltac zlit :=
  repeat match goal with
         | |- context [Z_to_bv 64 ?z] =>
             lazymatch z with
             | Z0 => fail | Zpos _ => fail | Zneg _ => fail
             | _ => check_closed_term z; let z' := eval vm_compute in z in change z with z'
             end
         end.

(* [comment removed for export] *)
Ltac len_rw :=
  repeat match goal with
         | |- context [length (word_to_le_bytes ?n ?v)] => rewrite (length_N_to_le_bytes n v)
         | |- context [length (zeros ?n)] => rewrite (length_zeros n)
         | |- context [length (repeat ?x ?n)] => rewrite (repeat_length x n)
         end.

(* [comment removed for export] *)
(* OLD: unfold win_lo;   NEW: try unfold win_lo; try unfold wok_lo; try unfold
   stack_window_reach;
   store_ok_cmem_win (MemSplit.v:306-309) asks 'wok_lo sp0 <= bv_unsigned a', and
   wok_lo (MemSplit.v:123-124) is 'bv_unsigned sp0 + stack_window_reach -
   stack_max_size' - a STRICTLY TIGHTER bound than win_lo, as MemSplit.v:129-130's
   win_lo_le_wok_lo records.  region_side unfolded only win_lo, so on that side
   condition wok_lo stayed folded, lia saw an opaque atom it could not relate to
   bv_unsigned sp0, and answered "Cannot find witness" - the error at seven sites:
   AsanInit.v:282 (fixed separately, a stale constant), RefStartup1.v:136,
   RefStartup3.v:97, RefStartup4.v:209, UbStartup1.v:132, UbStartup3.v:96,
   UbStartup4.v:207.  The tree already unfolds it this way where it is written out by
   hand: StoreOk.v:760 'unfold stack_window_reach, stack_max_size; u_norm; lia'.
   Each unfold is under [try] because region_side runs on BOTH side conditions of
   store_ok_cmem_win and the second mentions none of these constants; a bare [unfold]
   of an absent constant is an error. *)
Ltac region_side :=
  try unfold win_lo; try unfold wok_lo; try unfold stack_window_reach;
  match goal with |- context [stack_max_size] => rewrite ?stack_max_size_val | _ => idtac end;
  len_rw;
  cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul]; imm_norm; unorm; lia.

(* [comment removed for export] *)
Ltac addr_norm :=
  gres; pin; imm_norm; rewrite ?v_addi_0; unfold v_addi, v_add; unorm; zlit.

(* [comment removed for export] *)
Ltac vclose_fin :=
  first [ reflexivity | f_equal; lia | apply at_self | symmetry; apply at_self
        | apply Z_to_bv_u_eq; lia | apply Z_to_bv_u_eq_sym; lia | bveq ].
Ltac vclose :=
  gres; pin; imm_norm;
  first [ reflexivity
        | unfold v_addi, v_add; unorm; zlit; vclose_fin
        | rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l; first [ reflexivity | vclose_fin ]
        | rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l; unfold v_addi, v_add; unorm; zlit; vclose_fin ].

(* [comment removed for export] *)
Ltac with_mem_hidden_raw tac :=
  lazymatch goal with
  | |- msteps _ (mkst _ _ ?m _) _ =>
      let M := fresh "MEMH" in set (M := m); tac (); subst M
  | |- _ => tac ()
  end.
(* [comment removed for export] *)
Ltac with_mem_hidden tac := with_tgt_hidden ltac:(fun _ => with_mem_hidden_raw tac).

(* [comment removed for export] *)
Ltac sn F D := with_mem_hidden ltac:(fun _ => stepn F D; pin).
Ltac sv F D v := with_tgt_hidden ltac:(fun _ => stepiv F D v vclose).   (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac stepb_tk F D tac := with_mem_hidden ltac:(fun _ => WalkTac.stepb_tk F D tac).
Ltac stepb_ft F D tac := with_mem_hidden ltac:(fun _ => WalkTac.stepb_ft F D tac).

(* [comment removed for export] *)
Ltac blit :=
  repeat match goal with
         | |- context [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 ?z))] =>
             lazymatch z with
             | Z0 => change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 0)
             | Zpos _ => let z' := eval vm_compute in (z mod 256)%Z in
                         change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 z')
             end
         end.

(* [comment removed for export] *)
Ltac push_store :=
  blit;
  first [ rewrite wbytes_cmem_win by region_side
        | rewrite wbytes_cmem_data by region_side
        | idtac ].

(* [comment removed for export] *)
Ltac stw_raw F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Store SZ8 _ _ _, _) =>
        eapply step_sd_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | vclose | vclose | oktac ]
    | decode_any _ = Some (Store SZ4 _ _ _, _) =>
        eapply step_sw_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | vclose | vclose | oktac ]
    | decode_any _ = Some (Store SZ2 _ _ _, _) =>
        eapply step_sh_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | vclose | vclose | oktac ]
    | decode_any _ = Some (Store SZ1 _ _ _, _) =>
        eapply MmapSim.step_sb_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | vclose | vclose | reflexivity | oktac ]
    end
  | step_simpl; push_store ].
Ltac stw F D aa vv oktac := with_tgt_hidden ltac:(fun _ => stw_raw F D aa vv oktac).   (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac ok_sub Hok :=
  store_ok_peel; eapply store_ok_sub; [ | exact Hok | | ];
  rewrite ?length_N_to_le_bytes, ?length_zeros; unorm; lia.

(* [comment removed for export] *)
Lemma wfJ_wb_chain : forall sp0 J l M, M = wb_chain J l -> wfJ sp0 J -> wfJ sp0 M.
Proof. intros sp0 J l M -> H x Hx. apply wb_chain_grows. apply H. exact Hx. Qed.
(* [comment removed for export] *)
Ltac ok_win HJ :=
  apply store_ok_cmem_win;
  [ first [ lazymatch goal with
            | |- wfJ ?sp0 ?M =>
                lazymatch M with wbytes (wbytes _ _ _) _ _ => idtac end;
                let l := wb_ulist M in
                let m := wb_base M in
                exact (wfJ_wb_chain sp0 m l M (@eq_refl wb_mem M) HJ)
            end
          | repeat apply wfJ_wbytes; exact HJ ]
  | region_side | region_side ].

(* [comment removed for export] *)
Ltac ok_data :=
  apply store_ok_cmem_data;
  lazymatch goal with |- ?g => check_closed_term g; vm_compute; reflexivity end.

(* [comment removed for export] *)
Ltac ld_step_raw F D bsv vv rdtac valtac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Load SZ8 _ _ _ _, _) => eapply step_ld with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ4 true _ _ _, _) => eapply step_lw with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ4 false _ _ _, _) => eapply step_lwu with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ2 true _ _ _, _) => eapply step_lh with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ2 false _ _ _, _) => eapply step_lhu with (bs := bsv) (v := vv)
    end;
    [ exact F | reflexivity | exact D | addr_norm; rdtac | valtac ]
  | step_simpl ]; vnorm; pin.
Ltac ld_step F D bsv vv rdtac valtac := with_tgt_hidden ltac:(fun _ => ld_step_raw F D bsv vv rdtac valtac).   (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac lb_step_raw F D bb rdtac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Load SZ1 false _ _ _, _) => eapply step_lbu with (b := bb)
    | decode_any _ = Some (Load SZ1 true _ _ _, _) => eapply step_lb with (b := bb)
    end;
    [ exact F | reflexivity | exact D | addr_norm; rdtac ]
  | step_simpl ]; vnorm; pin.
Ltac lb_step F D bb rdtac := with_tgt_hidden ltac:(fun _ => lb_step_raw F D bb rdtac).   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rdn_wbytes_out_Z : forall segs bs m (zb za : Z) n,
  (0 <= za < 2^64 /\ za + Z.of_nat n <= 2^64 /\ 0 <= zb < 2^64 /\
   zb + Z.of_nat (length bs) <= 2^64 /\
   (za + Z.of_nat n <= zb \/ zb + Z.of_nat (length bs) <= za))%Z ->
  rdn segs (wbytes m (Z_to_bv 64 zb) bs) (Z_to_bv 64 za) n = rdn segs m (Z_to_bv 64 za) n.
Proof.
  intros segs bs m zb za n (Ha & Han & Hb & Hbn & Hd).
  apply rdn_wbytes_out; rewrite ?u_Z2bv by lia; lia.
Qed.

Ltac len_simpl :=
  len_rw; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul Pos.add Pos.mul].

Ltac peel :=
  try peel_refl;   (* [comment removed for export] *)
  repeat first [ rewrite rdn_wbytes_out_Z by (len_simpl; lia)
               | rewrite rdn_wbytes_out by region_side ].

(* [comment removed for export] *)
Ltac rd_img L := addr_norm; rewrite rdn_cmem_data by region_side; peel; exact L.

(* [comment removed for export] *)
Ltac rd_hit8 :=
  addr_norm; peel;
  lazymatch goal with |- rdn _ (wbytes _ ?a' _) ?a _ = _ =>
    first [ constr_eq a a' | replace a with a' by (first [f_equal; lia | bveq]) ] end;
  apply rdn_wbytes_hit8; unorm; lia.

(* [comment removed for export] *)
Ltac in_list := cbn [In]; repeat first [ left; reflexivity | right ].
Ltac solve_regs_agree :=
  repeat (apply regs_agree_upd; [ in_list | ]); apply regs_agree_refl.

(* [comment removed for export] *)
Ltac incl_list :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [In] in Hr;
  repeat (destruct Hr as [<-|Hr]; [in_list|]); destruct Hr.
Ltac regs_agree_weaken Hag :=
  eapply regs_agree_mono; [| exact Hag]; incl_list.

Ltac notin_list :=
  cbn [In]; intros HH; repeat (destruct HH as [HH|HH]; [apply bv_eq in HH; cbv in HH; discriminate HH|]); exact HH.

(* [comment removed for export] *)
Ltac carry Hag H r T :=
  pose proof (Hag r ltac:(notin_list)) as T;
  repeat first [ rewrite getr_same in T by reg_neq_tac | rewrite getr_other in T by reg_neq_tac ];
  rewrite ?H in T.

(* [comment removed for export] *)
Ltac ra_chain :=
  first [ apply regs_agree_refl
        | apply regs_agree_upd; [ in_list | ]; ra_chain
        | match goal with
          | Hag : regs_agree _ _ ?r |- regs_agree _ _ ?r =>
              eapply regs_agree_trans; [ | regs_agree_weaken Hag ]; ra_chain
          end ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition bwd (segs : list Segment) (G : machine_state -> Prop) : Prop :=
  forall st st', msteps segs st st' -> G st' -> G st.

Lemma bwd_msteps : forall segs tgt, bwd segs (fun st => msteps segs st tgt).
Proof. intros segs tgt st st' H1 H2. eapply msteps_trans; eassumption. Qed.

(* A walk over the binary's own segments is the same walk over the run's
   segment list ([StoreOk.step_run_segments]), so a goal closed backwards
   over [run_segments] is closed backwards over the binary's walk. *)
Lemma msteps_run_segments : forall segs inp (sp mbase : word) st st',
  msteps segs st st' -> msteps (run_segments segs inp sp mbase) st st'.
Proof.
  intros segs inp sp mbase st st' H.
  induction H as [ms | ms ms' ms'' Hs Hstep _ IH]; [apply mst_refl|].
  eapply mst_step; [exact Hs | apply step_run_segments; exact Hstep | exact IH].
Qed.

Lemma bwd_run_segments : forall segs inp (sp mbase : word) G,
  bwd (run_segments segs inp sp mbase) G -> bwd segs G.
Proof.
  intros segs inp sp mbase G HG st st' Hm HG'.
  apply (HG st st'); [apply msteps_run_segments; exact Hm | exact HG'].
Qed.

(* A store of bytes the memory already holds changes nothing. *)
Lemma wbytes_same_m : forall bs m (a : word),
  (bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  (forall j, (j < length bs)%nat ->
     m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0))) ->
  wbytes m a bs = m.
Proof.
  intros bs m a Hnw Hall. apply functional_extensionality. intros x.
  pose proof (u64_range x) as Hx. pose proof (u64_range a) as Ha.
  destruct (Z_lt_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge].
  { apply wbytes_outside; lia. }
  destruct (Z_lt_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [Hin|Hout].
  2: { apply wbytes_outside; lia. }
  rewrite wbytes_inside by lia.
  assert (Hxj : x = Z_to_bv 64 (bv_unsigned a
                     + Z.of_nat (Z.to_nat (bv_unsigned x - bv_unsigned a)))).
  { apply bv_eq. rewrite u_Z2bv by lia. lia. }
  rewrite Hxj at 2. symmetry. apply Hall. lia.
Qed.

(* [comment removed for export] *)
Ltac gsteps HG := eapply HG.
