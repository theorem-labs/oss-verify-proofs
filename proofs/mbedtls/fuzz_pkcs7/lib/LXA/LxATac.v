(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem MState Cells Step CellsX Frame PropExec Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow AEvtA ARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import StepA TacA.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac lx_pins_hook := idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_LxATac () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.zswrap"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.zlow"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_wf"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_bytes"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le4"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"].


Lemma zlow64_range : forall x, 0 <= zlow 64 x < 2^64.
Proof. intros x. unfold zlow. apply Z.mod_pos_bound. reflexivity. Qed.


Lemma byte_range : forall (b : bv 8), 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. replace 256 with (bv_modulus 8) by (vm_compute; reflexivity). exact H. Qed.

Lemma b8_of_unsigned : forall (b : bv 8), Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* [comment removed for export] *)
Lemma lx_xor_eq : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> 0 <= - zlow 64 (Z.lxor a b) -> a = b.
Proof.
  intros a b Ha Hb H. pose proof (Z_lxor_range a b Ha Hb) as R. unfold zlow in H. rewrite Z.mod_small in H by exact R.
  apply lxor_small_eq; lia.
Qed.

(* [comment removed for export] *)
Ltac lx_cells_norm :=
  repeat match goal with
         | H : context [C1 ?b] |- _ =>
             lazymatch b with
             | Z_to_bv _ _ => fail
             | _ => rewrite <- (b8_of_unsigned b) in H;
                    let u := fresh "lxu" in let R := fresh "lxRu" in
                    pose proof (byte_range b) as R;
                    set (u := bv_unsigned b) in *; clearbody u
             end
         end.

(* [comment removed for export] *)
Definition lx_hidden (P : Prop) : Prop := P.
Ltac lx_hide1 H := lazymatch type of H with ?T => change (lx_hidden T) in H end.
Ltac lx_unhide := repeat match goal with H : lx_hidden ?T |- _ => unfold lx_hidden in H end.
(* [comment removed for export] *)
Definition lx_pinned (P : Prop) : Prop := P.
(* [comment removed for export] *)
Definition lx_wdecl (P : Prop) : Prop := P.
(* [comment removed for export] *)
Ltac lx_pin1 H := first [ clear H | lazymatch type of H with ?T => lazymatch T with lx_pinned _ => idtac | lx_hidden _ => idtac | _ => change (lx_pinned T) in H end end ].
Ltac lx_unpin := repeat match goal with H : lx_pinned ?T |- _ => unfold lx_pinned in H end.
(* [comment removed for export] *)
Ltac lx_pin1k H := lazymatch type of H with ?T => lazymatch T with lx_pinned _ => idtac | lx_hidden _ => idtac | _ => change (lx_pinned T) in H end end.

(* [comment removed for export] *)
Ltac lx_prune :=
  repeat match goal with
         | H : rw_cells _ _ _ _ |- _ => clear H | H : ro_cells _ _ _ _ |- _ => clear H | H : bytes_at _ _ _ _ |- _ => clear H
         | H : stk _ _ _ _ |- _ => clear H | H : aobj _ _ _ _ _ _ |- _ => clear H | H : crange _ _ _ |- _ => clear H
         | H : munch _ _ _ |- _ => clear H | H : wmono _ _ _ |- _ => clear H | H : mem_inv _ _ |- _ => clear H
         | H : abase _ _ _ |- _ => clear H | H : cs_ok _ _ |- _ => clear H | H : asan_img_ok _ |- _ => clear H
         | H : al_wf _ |- _ => clear H
         (* [comment removed for export] *)
         | H : _ = true |- _ => clear H | H : _ = false |- _ => clear H
         | H : forall n : Z, _ |- _ => clear H
         | H : lx_hidden _ |- _ => clear H | H : lx_pinned _ |- _ => clear H | H : lx_wdecl _ |- _ => clear H
         end.

(* [comment removed for export] *)
Ltac lx_zlow_ranges :=
  rewrite ?lx_bvu64 in *;
  repeat match goal with
         | |- context [zlow 64 ?x] =>
             lazymatch goal with _ : 0 <= zlow 64 x < _ |- _ => fail | _ => pose proof (zlow64_range x) end
         | _ : context [zlow 64 ?x] |- _ =>
             lazymatch goal with _ : 0 <= zlow 64 x < _ |- _ => fail | _ => pose proof (zlow64_range x) end
         end.

(* [comment removed for export] *)
Ltac lx_clear_seps :=
  repeat match goal with
         | H : _ = 0 \/ _ \/ _ |- _ => clear H
         | H : ?a + _ <= ?r \/ _ <= ?a |- _ => lazymatch r with Z0 => fail | _ => clear H end
         end.

(* [comment removed for export] *)
Ltac lx_clear_seps_nz :=
  repeat match goal with H : _ + 1 <= 0 \/ 0 + 1 <= _ |- _ => clear H end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lx_nz_norm :=
  repeat match goal with
         | H : ?x + 1 <= 0 \/ 0 + 1 <= ?x |- _ =>
             first [ assert (1 <= x) by (destruct H as [H|H]; [exfalso| exact H]; clear_disj; lx_zlow_ranges; lia); clear H
                   | revert H ]   (* [comment removed for export] *)
         end;
  intros.

Lemma bvu64_range : forall w : bv 64, 0 <= bv_unsigned w < 2^64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H. exact H. Qed.

(* [comment removed for export] *)
Ltac lx_bvu_ranges :=
  repeat match goal with
         | |- context [bv_unsigned ?w] =>
             lazymatch goal with _ : 0 <= bv_unsigned w < _ |- _ => fail | _ => pose proof (bvu64_range w) end
         | _ : context [bv_unsigned ?w] |- _ =>
             lazymatch goal with _ : 0 <= bv_unsigned w < _ |- _ => fail | _ => pose proof (bvu64_range w) end
         end.

(* [comment removed for export] *)
Lemma lx_zswrap32_errsum : ltac2:(CDefT.buildp (gd_tbl_LxATac ()) "Pr,$0.Pc,$0.Pk,$0.P,(1.$0.R1.(2.+10000000000000000.R2.))P,(3.(4.=R3.)(4.R3.+40000000.))P,(3.(5.-40000000.R5.)(5.R5.=))(1.$0.(6.+20.(7.+20.(8.R6.R4.)))(2.R6.R5.))")
(* [comment removed for export] *).
Proof.
  intros r c k -> Hc Hr. unfold zswrap, zlow.
  change (2 ^ 32) with 4294967296. change (2 ^ (32 - 1)) with 2147483648.
  replace (r + (18446744073709551616 - c)) with ((r - c) + 4294967296 * 4294967296) by lia.
  rewrite Z_mod_plus_full.
  rewrite <- (Z.mod_unique (r - c) 4294967296 (-1) (r - c + 4294967296)) by lia.
  rewrite <- (Z.mod_unique (r - c + 4294967296 + 2147483648) 4294967296 1 (r - c + 2147483648)) by lia.
  lia.
Qed.
Lemma lx_zlow64_nonpos_zero : forall r, -18446744073709551616 < r < 18446744073709551616 -> 0 <= - zlow 64 r -> r = 0.
Proof.
  intros r Hr Hz. unfold zlow in Hz. change (2 ^ 64) with 18446744073709551616 in Hz.
  destruct (Z.eq_dec r 0) as [E|NE]; [exact E|].
  destruct (Z.lt_ge_cases r 0).
  - rewrite <- (Z.mod_unique r 18446744073709551616 (-1) (r + 18446744073709551616)) in Hz by lia. lia.
  - rewrite Z.mod_small in Hz by lia. lia.
Qed.
Lemma lx_zlow64_pos_nonzero : forall r, 0 <= zlow 64 r + -1 -> r <> 0.
Proof. intros r H ->. unfold zlow in H. rewrite Z.mod_0_l in H; lia. Qed.
Lemma lx_zlow64_small_id : forall x, 0 <= x < 18446744073709551616 -> zlow 64 x = x.
Proof. intros x Hx. unfold zlow. apply Z.mod_small. exact Hx. Qed.

(* [comment removed for export] *)
Ltac lx_side := lx_prune; lx_clear_seps; lia.

(* [comment removed for export] *)
Ltac lx_errsum :=
  repeat match goal with
         | |- context [zswrap 32 (zlow 32 (?r + ?k))] =>
             lx_is_lit k; let c := eval vm_compute in (18446744073709551616 - k) in
             rewrite (lx_zswrap32_errsum r c k eq_refl) by lx_side
         | H : context [zswrap 32 (zlow 32 (?r + ?k))] |- _ =>
             lx_is_lit k; let c := eval vm_compute in (18446744073709551616 - k) in
             rewrite (lx_zswrap32_errsum r c k eq_refl) in H by lx_side
         end.
(* [comment removed for export] *)
Ltac lx_zlow_norm :=
  repeat match goal with
         | Hz : 0 <= - zlow 64 ?r |- _ =>
             is_var r; let E := fresh "R0" in assert (E : r = 0) by (apply lx_zlow64_nonpos_zero; [clear Hz; lx_side | exact Hz]); clear Hz
         | Hz : 0 <= zlow 64 ?r + -1 |- _ =>
             is_var r; let E := fresh "RNZ" in pose proof (lx_zlow64_pos_nonzero r Hz) as E; clear Hz
         end;
  (* [comment removed for export] *)
  repeat match goal with
         | |- context [zlow 64 ?x] => rewrite (lx_zlow64_small_id x) by lx_side
         end.

(* [comment removed for export] *)
Ltac lx_arith_core := first [lia | (unfold zlow, zswrap in *; lia)].

(* [comment removed for export] *)
Ltac lx_xor_norm :=
  repeat match goal with
         | H : 0 <= - zlow 64 (Z.lxor ?a ?b) |- _ =>
             apply lx_xor_eq in H; [| clear H; lx_bvu_ranges; lx_arith_core | clear H; lx_bvu_ranges; lx_arith_core]
         end.

(* [comment removed for export] *)
Ltac lx_imp_norm :=
  repeat match goal with
         | H : ?p -> _ |- _ =>
             lazymatch type of p with
             | Prop => let Hp := fresh "Hp" in
                       assert (Hp : p) by (clear H; lia); specialize (H Hp); clear Hp
             end
         end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lx_arith := lx_pins_hook; lx_prune; lx_clear_seps; lx_zlow_ranges; lx_nz_norm;
                 first [ lia | timeout 40 (unfold zlow, zswrap in *; lia)   (* timeout-ok: expiry takes the lx_errsum arm after it, which proves the same goal another way *)
                       | lx_errsum; lx_zlow_norm; lx_bvu_ranges; lx_xor_norm; first [lia | lx_imp_norm; lx_arith_core] ].

(* [comment removed for export] *)
Ltac lx_logic_atom := first [eassumption | reflexivity | lia].
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lx_open_ex H :=
  lazymatch type of H with
  | @ex _ _ => let x := fresh "w" in let H2 := fresh "Hw" in destruct H as [x H2]; lx_open_ex H2
  | _ /\ _ => let H1 := fresh "Hw" in let H2 := fresh "Hw" in destruct H as [H1 H2]; lx_open_ex H1; lx_open_ex H2
  | _ => idtac
  end.
Ltac lx_logic_light :=
  repeat match goal with H : exists _, _ |- _ => lx_open_ex H end;
  repeat match goal with |- exists _, _ => eexists end;
  repeat match goal with |- _ /\ _ => split end;
  first [ lx_logic_atom
        | match goal with H : _ \/ _ |- _ \/ _ => let H1 := fresh "Hd" in destruct H as [H1|H1]; [left | right]; lx_open_ex H1; repeat split; lx_logic_atom end
        | left; repeat split; lx_logic_atom
        | right; repeat split; lx_logic_atom ].
(* [comment removed for export] *)
Lemma lx_uw64 : forall x, 0 <= x -> x <= 18446744073709551615 -> bv_unsigned (Z_to_bv 64 x) = x.
Proof. intros x H1 H2. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.
Ltac lx_uw_norm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (lx_uw64 x) by (lx_prune; clear_disj; lia)
         | H : context [bv_unsigned (Z_to_bv 64 ?x)] |- _ => rewrite (lx_uw64 x) in H by (lx_prune; clear_disj; lia)
         end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lx_ends1 t := lazymatch t with Z.add _ ?b => lx_ends1 b | 1 => idtac end.
Ltac lx_is_postcase T := match T with context [?x <= 0] => lx_ends1 x end.
Ltac lx_clear_seps_but_post :=
  repeat match goal with
         | H : ?T |- _ => lazymatch T with
                          | _ \/ _ => tryif lx_is_postcase T then fail else clear H
                          end
         end.
(* [comment removed for export] *)
Ltac lx_refute_closed a n := assert (n : ~ a) by (clear; intro; lia).
Ltac lx_disj_prune :=
  repeat match goal with
  | H : ?a \/ ?b |- _ =>
      let n := fresh "n" in let H' := fresh "Hd" in
      first [ lx_refute_closed a n;
              assert (H' : b) by (destruct H as [H|H]; [exact (False_ind _ (n H)) | exact H]);
              clear n H; rename H' into H
            | lx_refute_closed b n;
              assert (H' : a) by (destruct H as [H|H]; [exact H | exact (False_ind _ (n H))]);
              clear n H; rename H' into H
            | lazymatch b with ?b1 \/ ?b2 =>
                lx_refute_closed b1 n;
                assert (H' : a \/ b2) by (destruct H as [H|[H|H]]; [left; exact H | exact (False_ind _ (n H)) | right; exact H]);
                clear n H; rename H' into H
              end ]
  end.
(* [comment removed for export] *)
Ltac lx_imp_subst G :=
  try (lazymatch type of G with ?a = ?b => first [ is_var a; subst a | is_var b; subst b | idtac ] end).
Ltac lx_logic :=
  intros; lx_prune; lx_disj_prune;
  first [ lx_clear_seps; lx_uw_norm; lx_logic_light
        | lx_clear_seps; lx_errsum; lx_zlow_norm; lx_zlow_ranges; lx_bvu_ranges; lx_xor_norm; lx_imp_norm; lx_uw_norm; lx_logic_light
        (* [comment removed for export] *)
        | lx_clear_seps_but_post; lx_uw_norm; lx_errsum; lx_zlow_norm; lx_imp_norm; lx_logic_light
        | lx_clear_seps; exfalso; lia ].

(* [comment removed for export] *)
Ltac lx_hm_at :=
  lazymatch goal with |- HM ?segs ?R ?HIA ?h ?LB ?LF ?mx =>
    match goal with HH : HM segs R HIA h LB LF ?m0, MU : munch ?W ?m0' mx, WM : wmono _ ?m0'' mx |- _ =>
      eapply (hm_munch segs R HIA h LB LF W m0 mx); [exact HH | exact MU | exact WM | solve_w_writable] end end.
(* [comment removed for export] *)
Ltac lx_munch_join :=
  lazymatch goal with |- munch ?W ?ma ?mx =>
    match goal with M1 : munch W ma ?mb, M2 : munch ?W2 ?mb' mx |- _ =>
      constr_eq mb mb';
      apply (munch_trans W ma mb mx M1); eapply munch_weaken; [| exact M2];
      unfold sub_fp; cbn [outside fst snd]; let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; clear - Hx; lia
    end end.
Ltac lx_munch_join_ctx :=
  lazymatch goal with |- munch ?W ?ma ?mx =>
    match goal with M1 : munch W ma ?mb, M2 : munch ?W2 ?mb' mx |- _ =>
      constr_eq mb mb';
      apply (munch_trans W ma mb mx M1); eapply munch_weaken; [| exact M2];
      unfold sub_fp; cbn [outside fst snd]; lx_prune; lx_clear_seps; intros; lia
    end end.
Ltac lx_wmono_join :=
  lazymatch goal with |- wmono ?segs ?ma ?mx =>
    match goal with W1 : wmono segs ma ?mb, W2 : wmono segs ?mb' mx |- _ =>
      constr_eq mb mb'; exact (wmono_trans segs ma mb mx W1 W2) end end.
(* [comment removed for export] *)
Ltac lx_rebase mx :=
  lazymatch goal with |- context [MS _ _ _ _ _ mx (seg_rom ?segs)] =>
    pose proof (munch_refl [] mx : munch [] mx mx); pose proof (wmono_refl segs mx : wmono segs mx mx) end.


(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lx_solve_in := lazymatch goal with |- In _ _ => cbn; repeat (first [left; first [reflexivity | lia] | right]) end.
Ltac lx_is_mem_goal :=
  lazymatch goal with
  | |- rw_cells _ _ _ _ => idtac | |- ro_cells _ _ _ _ => idtac | |- bytes_at _ _ _ _ => idtac | |- stk _ _ _ _ => idtac
  | |- aobj _ _ _ _ _ _ => idtac | |- munch _ _ _ => idtac | |- wmono _ _ _ => idtac | |- mem_inv _ _ => idtac
  | |- HM _ _ _ _ _ _ _ => idtac | |- abase _ _ _ => idtac
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lx_app_hook := fail.
(* [comment removed for export] *)
Ltac lx_spine := lazymatch goal with |- _ /\ _ => split; [| lx_spine] | |- _ => idtac end.
(* [comment removed for export] *)
Ltac lx_head t := lazymatch t with ?f _ => lx_head f | _ => t end.
Ltac lx_is_bundle :=
  first [ lx_is_mem_goal; fail 1 | idtac ];
  lazymatch goal with
  | |- _ /\ _ => fail
  | |- ?g => let h0 := lx_head g in is_const h0;
             lazymatch h0 with
             | @Z.le => fail | @Z.lt => fail | @eq => fail | @crange => fail | @sshad => fail | @presW => fail
             (* [comment removed for export] *)
             | @evtA => fail | @not => fail | @or => fail
             | _ => let g' := eval hnf in g in lazymatch g' with _ /\ _ => idtac end
             end
  end.
(* [comment removed for export] *)
Ltac lx_imp_absurd G :=
  lazymatch type of G with
  | ?r = _ => is_var r; subst r;
      match goal with
      | K : _ = true |- _ => cbn in K; discriminate K
      | K : _ = false |- _ => cbn in K; discriminate K
      end
  | _ = ?r => is_var r; subst r;
      match goal with
      | K : _ = true |- _ => cbn in K; discriminate K
      | K : _ = false |- _ => cbn in K; discriminate K
      end
  end.
(* [comment removed for export] *)
Ltac lx_spine_norm cs :=
  let h := eval hnf in cs in
  lazymatch h with
  | cons ?c ?r => let r' := lx_spine_norm r in constr:(@cons cell c r')
  | nil => constr:(@nil cell)
  end.
Ltac lx_spine_explicit cs :=
  lazymatch cs with
  | cons _ ?r => lx_spine_explicit r
  | nil => idtac
  end.
Ltac lx_cells_unfold :=
  repeat match goal with
  | H : rw_cells ?sg ?m ?a ?cs |- _ =>
      tryif lx_spine_explicit cs then fail
      else (let cs' := lx_spine_norm cs in progress change (rw_cells sg m a cs') in H)
  end.
(* [comment removed for export] *)
Ltac lx_goal_cells_unfold :=
  lazymatch goal with
  | |- rw_cells ?sg ?m ?a ?cs =>
      tryif lx_spine_explicit cs then idtac
      else (let cs' := lx_spine_norm cs in change (rw_cells sg m a cs'))
  | |- _ => idtac
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lx_side_lia := lx_pins_hook; lx_prune; lx_bvu_ranges; lia.

(* [comment removed for export] *)
Ltac lx_stk_glue n :=
  lazymatch n with
  | O => fail
  | S ?k =>
    lazymatch goal with
    | |- stk ?sg ?m ?a ?b =>
      first
      [ eassumption
      (* [comment removed for export] *)
      | first [ replace a with b by (clear; lia) | replace b with a by (clear; lia) ]; apply stk_empty; lx_prune; lx_bvu_ranges; lia
      | match goal with H : stk sg m ?c b |- _ => replace a with c by (clear; lia); exact H end
      | match goal with H : stk sg m ?c ?d |- _ =>
          replace a with c by (clear; lia);
          apply (stk_merge sg m c d b); [ exact H | lx_stk_glue k | ]
        end
      | match goal with H : rw_cells sg m ?c ?cs |- _ =>
          replace a with c by (clear; lia);
          apply (stk_merge sg m c (c + Z.of_nat (cells_size cs)) b);
          [ apply stk_of_rw_cells; exact H | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; lx_stk_glue k | ]
        end ]
    end
  end.
Ltac lx_stk_glue_top :=
  lx_stk_glue 8%nat; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; lx_prune; lx_clear_seps; lia.

Ltac lx_app :=
  lazymatch goal with
  | |- _ -> _ => first [ eassumption
                       | let G := fresh "G" in intro G;
                         first [ exfalso; clear - G; lia | exfalso; lx_imp_absurd G
                               | exfalso; lx_prune; lx_clear_seps; timeout 3 lia     (* [comment removed for export] *)   (* timeout-ok: fast tier: expiry takes the lx_imp_subst arm after it, which proves the goal another way *)
                               (* [comment removed for export] *)
                               | lx_imp_subst G; lx_disj_prune; lx_spine; lx_app ] ]
  | |- @ex _ _ => first [ eassumption | lx_logic ]
  (* [comment removed for export] *)
  | |- _ /\ _ => first [ eassumption | lx_spine; lx_app ]
  | |- _ =>
  (* [comment removed for export] *)
  tryif lx_is_mem_goal then (lx_goal_cells_unfold; first [ eassumption | lx_app_hook | lx_hm_at
                                  | lazymatch goal with |- munch _ _ _ => first [lx_munch_join | lx_munch_join_ctx] | |- wmono _ _ _ => lx_wmono_join
                                                      | |- stk _ _ _ _ => lx_stk_glue_top end ])
  else
  first [ eassumption | reflexivity | lx_weq
        | lx_is_bundle; hnf; lx_spine; lx_app
        | lx_app_hook
        | lx_arith | lx_lia
        | lazymatch goal with
          | |- In _ _ => lx_solve_in
          | |- HM _ _ _ _ _ _ _ => lx_hm_at
          | |- munch _ _ _ => first [lx_munch_join | lx_munch_join_ctx]
          | |- wmono _ _ _ => lx_wmono_join
          | |- _ => lx_logic
          end ]
  end.
(* [comment removed for export] *)
Lemma mkR_eq31 : ltac2:(CDefT.buildp (gd_tbl_LxATac ()) "Px1,(9.&40.)Px2,(9.&40.)Px3,(9.&40.)Px4,(9.&40.)Px5,(9.&40.)Px6,(9.&40.)Px7,(9.&40.)Px8,(9.&40.)Px9,(9.&40.)Px10,(9.&40.)Px11,(9.&40.)Px12,(9.&40.)Px13,(9.&40.)Px14,(9.&40.)Px15,(9.&40.)Px16,(9.&40.)Px17,(9.&40.)Px18,(9.&40.)Px19,(9.&40.)Px20,(9.&40.)Px21,(9.&40.)Px22,(9.&40.)Px23,(9.&40.)Px24,(9.&40.)Px25,(9.&40.)Px26,(9.&40.)Px27,(9.&40.)Px28,(9.&40.)Px29,(9.&40.)Px30,(9.&40.)Px31,(9.&40.)Py1,(9.&40.)Py2,(9.&40.)Py3,(9.&40.)Py4,(9.&40.)Py5,(9.&40.)Py6,(9.&40.)Py7,(9.&40.)Py8,(9.&40.)Py9,(9.&40.)Py10,(9.&40.)Py11,(9.&40.)Py12,(9.&40.)Py13,(9.&40.)Py14,(9.&40.)Py15,(9.&40.)Py16,(9.&40.)Py17,(9.&40.)Py18,(9.&40.)Py19,(9.&40.)Py20,(9.&40.)Py21,(9.&40.)Py22,(9.&40.)Py23,(9.&40.)Py24,(9.&40.)Py25,(9.&40.)Py26,(9.&40.)Py27,(9.&40.)Py28,(9.&40.)Py29,(9.&40.)Py30,(9.&40.)Py31,(9.&40.)P,(1.(9.&40.)R3>.R1?.)P,(1.(9.&40.)R3>.R1?.)P,(1.(9.&40.)R3>.R1?.)P,(1.(9.&40.)R3>.R1?.)P,(1.(9.&40.)R3>.R1?.)P,(1.(9.&40.)R3>.R1?.)P,(1.(9.&40.)R3>.R1?.)P,(1.(9.&40.)R3>.R1?.)P,(1.(9.&40.)R3>.R1?.)P,(1.(9.&40.)R3>.R1?.)P,(1.(9.&40.)R3>.R1?.)P,(1.(9.&40.)R3>.R1?.)P,(1.(9.&40.)R3>.R1?.)P,(1.(9.&40.)R3>.R1?.)P,(1.(9.&40.)R3>.R1?.)P,(1.(9.&40.)R3>.R1?.)P,(1.(9.&40.)R3>.R1?.)P,(1.(9.&40.)R3>.R1?.)P,(1.(9.&40.)R3>.R1?.)P,(1.(9.&40.)R3>.R1?.)P,(1.(9.&40.)R3>.R1?.)P,(1.(9.&40.)R3>.R1?.)P,(1.(9.&40.)R3>.R1?.)P,(1.(9.&40.)R3>.R1?.)P,(1.(9.&40.)R3>.R1?.)P,(1.(9.&40.)R3>.R1?.)P,(1.(9.&40.)R3>.R1?.)P,(1.(9.&40.)R3>.R1?.)P,(1.(9.&40.)R3>.R1?.)P,(1.(9.&40.)R3>.R1?.)P,(1.(9.&40.)R3>.R1?.)(1.(:.&5.(9.&40.))(;.R5=.R5<.R5;.R5:.R59.R58.R57.R56.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.)(;.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.))")
(* [comment removed for export] *).
Proof. intros. subst. reflexivity. Qed.
Lemma lx_MS_regs : ltac2:(CDefT.buildp (gd_tbl_LxATac ()) "PR,(:.&5.(9.&40.))PR',(:.&5.(9.&40.))PF,(:.&5.(9.&40.))Ppc,(9.&40.)Pfc,(9.&20.)Psv,(<.(9.&40.))Pm,P,(9.&40.)(<.(9.&8.))Prom,P,(9.&40.)(<.(9.&8.))P,(1.(:.&5.(9.&40.))R8.R7.)(1.$=.(>.R9.R7.R6.R5.R4.R3.R2.)(>.R8.R7.R6.R5.R4.R3.R2.))")
(* [comment removed for export] *).
Proof. intros. subst. reflexivity. Qed.
Ltac lx_regs_eq :=
  lazymatch goal with
  | |- mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) | idtac ]
  end.
(* [comment removed for export] *)
Tactic Notation "lx_apply" uconstr(L) :=
  first [ (eapply L; first [lx_is_mem_goal; eassumption | lazymatch goal with |- @eq (bv _) _ _ => reflexivity end | idtac])
        | (eapply evtA_eq; [ apply lx_MS_regs | eapply L; first [lx_is_mem_goal; eassumption | lazymatch goal with |- @eq (bv _) _ _ => reflexivity end | idtac] ])
        (* [comment removed for export] *)
        | (eapply aevtA_eq; [ apply lx_MS_regs | eapply L; first [lx_is_mem_goal; eassumption | lazymatch goal with |- @eq (bv _) _ _ => reflexivity end | idtac] ]) ];
  try lx_regs_eq; lx_app.
(* [comment removed for export] *)
Tactic Notation "lx_via_eq" tactic3(tac) :=
  first [ tac
        | lazymatch goal with
          | |- aevtA _ _ _ => eapply aevtA_eq; [ apply lx_MS_regs | tac ]
          | |- evtA _ _ _ _ _ => eapply evtA_eq; [ apply lx_MS_regs | tac ]
          end ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lx_conj_has_ex g :=
  lazymatch g with
  | ex _ => idtac
  | @eq machine_state _ _ => idtac
  (* [comment removed for export] *)
  | rw_cells _ _ _ _ => idtac | bytes_at _ _ _ _ => idtac | stk _ _ _ _ => idtac | aobj _ _ _ _ _ _ => idtac
  | munch _ _ _ => idtac | mem_inv _ _ => idtac
  | ?a /\ ?b => first [ lx_conj_has_ex a | lx_conj_has_ex b ]
  end.
Ltac lx_post_hnf :=
  lazymatch goal with
  | |- ex _ => idtac
  | |- _ /\ _ => idtac
  | |- _ \/ _ => fail
  | |- @eq _ _ _ => fail
  | |- _ => hnf; lazymatch goal with |- ?g => lx_conj_has_ex g end
  end.
Ltac lx_post_open := repeat (lx_post_hnf; first [ lx_exs | progress lx_ands ]).
Ltac lx_ms_refl := lazymatch goal with |- @eq machine_state _ _ => reflexivity | |- _ => idtac end.
(* [comment removed for export] *)
Ltac lx_ms_regs_open :=
  lazymatch goal with
  | |- @eq machine_state _ _ => first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | idtac ] ]
  | |- _ => idtac
  end.
Ltac lx_post_body := lx_post_open; lx_ms_regs_open; try (lx_is_mem_goal; eassumption); try assumption; try (lx_is_mem_goal; eassumption); try (lazymatch goal with |- @eq (bv _) _ _ => lx_weq end).
Ltac lx_post_or :=
  lazymatch goal with
  | |- _ \/ _ => first [ (left; hnf; lx_post_or) | (right; hnf; lx_post_or) ]
  | |- _ => lx_post_body
  end.
Ltac lx_leaf :=
  first [ first [ apply evtA_done | apply evt_done ]; hnf; lx_post_or
        | lx_post ];
  first [lx_app | idtac].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lx_max_facts :=
  repeat match goal with
  | H : context [Z.max ?a ?b] |- _ =>
      lazymatch type of H with
      | _ <= _ => idtac | _ < _ => idtac | _ <= _ <= _ => idtac | _ <= _ < _ => idtac | _ = _ => idtac
      end;
      lazymatch goal with
      | _ : a <= Z.max a b |- _ => fail
      | |- _ => pose proof (Z.le_max_l a b); pose proof (Z.le_max_r a b)
      end
  end.
(* [comment removed for export] *)
Definition lx_impd (P : Prop) : Prop := True.
Ltac lx_imp_neg r NE :=
  match goal with
  | R' : (_ < r <= 0)%Z |- _ => clear - NE R'; lia
  | R' : (r <= 0)%Z |- _ => clear - NE R'; lia
  | R' : (_ < r /\ r <= 0)%Z |- _ => clear - NE R'; lia
  end.
(* [comment removed for export] *)
Ltac lx_have T := match goal with _ : T |- _ => idtac end.
Ltac lx_imp_lin r H Q :=
  lazymatch Q with
  | ?A /\ ?B =>
      lx_imp_lin r constr:(fun E : r = 0 => proj1 (H E)) A;
      lx_imp_lin r constr:(fun E : r = 0 => proj2 (H E)) B
  | (?a <= ?b)%Z =>
      let N := fresh "Hri" in
      first [ lx_have constr:(r + 1 <= 0 \/ a <= b)
            | assert (N : r + 1 <= 0 \/ a <= b) by (let E := fresh "E" in let NE := fresh "NE" in destruct (Z.eq_dec r 0) as [E|NE]; [right; exact (H E) | left; lx_imp_neg r NE]) | idtac ]
  | (?a < ?b)%Z =>
      let N := fresh "Hri" in
      first [ lx_have constr:(r + 1 <= 0 \/ a + 1 <= b)
            | assert (N : r + 1 <= 0 \/ a + 1 <= b) by (let E := fresh "E" in let NE := fresh "NE" in destruct (Z.eq_dec r 0) as [E|NE]; [right; pose proof (H E); lia | left; lx_imp_neg r NE]) | idtac ]
  | (?a = ?b :> Z) =>
      let N := fresh "Hri" in let N2 := fresh "Hri" in
      first [ lx_have constr:(r + 1 <= 0 \/ a <= b)
            | assert (N : r + 1 <= 0 \/ a <= b) by (let E := fresh "E" in let NE := fresh "NE" in destruct (Z.eq_dec r 0) as [E|NE]; [right; pose proof (H E); lia | left; lx_imp_neg r NE]) | idtac ];
      first [ lx_have constr:(r + 1 <= 0 \/ b <= a)
            | assert (N2 : r + 1 <= 0 \/ b <= a) by (let E := fresh "E" in let NE := fresh "NE" in destruct (Z.eq_dec r 0) as [E|NE]; [right; pose proof (H E); lia | left; lx_imp_neg r NE]) | idtac ]
  | _ => idtac
  end.
Ltac lx_imp_disj :=
  repeat match goal with
  | H : ?r = 0 -> ?Q |- _ =>
      lazymatch type of r with Z => idtac end;
      lazymatch goal with _ : lx_impd (r = 0 -> Q) |- _ => fail | |- _ => idtac end;
      pose proof (I : lx_impd (r = 0 -> Q));
      lx_imp_lin r H Q
  end;
  repeat match goal with M : lx_impd _ |- _ => clear M end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lx_clear_if_dup H :=
  let T := type of H in
  try match goal with H' : T |- _ => tryif constr_eq H H' then fail else clear H end.
Definition lx_frshd (P : Prop) : Prop := True.
Ltac lx_frsh_facts :=
  repeat match goal with
  | H : fresh_apart ?R ?LB ?LF ?N ?k |- _ =>
      lazymatch goal with
      | _ : lx_frshd (fresh_apart R LB LF N k) |- _ => fail
      | |- _ => pose proof (I : lx_frshd (fresh_apart R LB LF N k));
                let F := fresh "Hfr" in pose proof H as F; unfold fresh_apart in F;
                let A := fresh "Hfr" in let B := fresh "Hfr" in let C := fresh "Hfr" in
                destruct F as (A & B & C & _); lx_clear_if_dup A; lx_clear_if_dup B; lx_clear_if_dup C
      end
  end;
  repeat match goal with M : lx_frshd _ |- _ => clear M end.
(* [comment removed for export] *)
Ltac lx_ceil_fact :=
  lazymatch goal with
  | _ : 0x7fff7f800000 <= @alloc_ceiling _ |- _ => idtac
  | _ : context [@alloc_ceiling ?Ly] |- _ => pose proof (@alloc_ceiling_lo Ly)
  | |- _ => idtac
  end.
Definition lx_callmark : Prop := True.
(* [comment removed for export] *)
Ltac lx_dedup :=
  repeat match goal with
  (* [comment removed for export] *)
  | H : ?T, H2 : ?T |- _ =>
      lazymatch T with
      | LxImg _ _ => fail
      | lx_callmark => fail
      | _ => lazymatch type of T with Prop => clear H2 end
      end
  end.
(* [comment removed for export] *)
Ltac lx_dedup_mem :=
  repeat match goal with
  | H : rw_cells ?s ?m ?A ?cs, H2 : rw_cells ?s ?m ?A ?cs |- _ => clear H2
  | H : ro_cells ?s ?m ?A ?cs, H2 : ro_cells ?s ?m ?A ?cs |- _ => clear H2
  | H : bytes_at ?s ?m ?A ?bs, H2 : bytes_at ?s ?m ?A ?bs |- _ => clear H2
  | H : u8arr ?s ?m ?A ?xs, H2 : u8arr ?s ?m ?A ?xs |- _ => clear H2
  | H : stk ?s ?m ?lo ?hi, H2 : stk ?s ?m ?lo ?hi |- _ => clear H2
  | H : aobj ?s ?al ?cs ?m ?A ?n, H2 : aobj ?s ?al ?cs ?m ?A ?n |- _ => clear H2
  | H : sshad ?s ?al ?m ?lo ?hi, H2 : sshad ?s ?al ?m ?lo ?hi |- _ => clear H2
  | H : mem_inv ?s ?m, H2 : mem_inv ?s ?m |- _ => clear H2
  | H : abase ?s ?al ?m, H2 : abase ?s ?al ?m |- _ => clear H2
  end.
(* [comment removed for export] *)
Lemma rw_cells_CB_bytes_eq : ltac2:(CDefT.buildp (gd_tbl_LxATac ()) "Psegs,(?.$10.)Pm,P,(9.&40.)(<.(9.&8.))PA,$0.Ppre,(?.$11.)Pn,$12.Pbs,(?.(9.&8.))Pcs,(?.$11.)P,(13.R7.R6.R5.(14.$11.R4.(15.$11.(16.R3.R2.)(17.$11.))))P,(18.R2.)P,(1.(?.(9.&8.))(19.R3.)R4.)(13.R:.R9.R8.(14.$11.R7.R4.))")
(* [comment removed for export] *).
Proof.
  intros segs m A pre n bs cs [[Hwf Hb] Hw] Hwf2 E.
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 _]]. cbn in H2.
  rewrite cells_bytes_app in Hb. cbn [cells_bytes cbytes app] in Hb. rewrite app_nil_r in Hb.
  rewrite cells_size_app in Hw. cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw.
  split. { split. { apply cells_wf_app. split; [exact H1| exact Hwf2]. } rewrite cells_bytes_app, E. exact Hb. }
  rewrite cells_size_app. rewrite <- (cells_bytes_length cs Hwf2). rewrite E, H2. exact Hw.
Qed.

Lemma rw_cells_CB_le4 : ltac2:(CDefT.buildp (gd_tbl_LxATac ()) "Psegs,(?.$10.)Pm,P,(9.&40.)(<.(9.&8.))PA,$0.Ppre,(?.$11.)Pn,$12.Pw,(9.&40.)Pl,(?.(9.&8.))P,(13.R7.R6.R5.(14.$11.R4.(15.$11.(16.R3.(14.(9.&8.)(1:.R2.)R1.))(17.$11.))))(13.R8.R7.R6.(14.$11.R5.(15.$11.(1;.R3.)(15.$11.(16.(1<.(9.&8.)R2.)R2.)(17.$11.)))))")
(* [comment removed for export] *).
Proof.
  intros. eapply rw_cells_CB_bytes_eq; [exact H| cbn; repeat split; reflexivity| cbn [cells_bytes cbytes app]; rewrite app_nil_r; reflexivity].
Qed.
Lemma rw_cells_CB_le8 : ltac2:(CDefT.buildp (gd_tbl_LxATac ()) "Psegs,(?.$10.)Pm,P,(9.&40.)(<.(9.&8.))PA,$0.Ppre,(?.$11.)Pn,$12.Pw,(9.&40.)Pl,(?.(9.&8.))P,(13.R7.R6.R5.(14.$11.R4.(15.$11.(16.R3.(14.(9.&8.)(1=.R2.)R1.))(17.$11.))))(13.R8.R7.R6.(14.$11.R5.(15.$11.(1>.R3.)(15.$11.(16.(1<.(9.&8.)R2.)R2.)(17.$11.)))))")
(* [comment removed for export] *).
Proof.
  intros. eapply rw_cells_CB_bytes_eq; [exact H| cbn; repeat split; reflexivity| cbn [cells_bytes cbytes app]; rewrite app_nil_r; reflexivity].
Qed.
Lemma rw_cells_CB_nil : forall segs m A pre n,
  rw_cells segs m A (pre ++ [CB n []]) -> rw_cells segs m A pre.
Proof.
  intros. rewrite <- (app_nil_r pre). eapply rw_cells_CB_bytes_eq; [exact H| exact I| reflexivity].
Qed.

(* [comment removed for export] *)
Ltac lx_last_split cs :=
  lazymatch cs with
  | [?c] => constr:((@nil cell, c))
  | ?c :: ?r => lazymatch lx_last_split r with (?p, ?l) => constr:((c :: p, l)) end
  end.
Ltac lx_cb_words :=
  repeat match goal with
  | H : rw_cells ?sg ?m ?A ?cs |- _ =>
      lazymatch lx_last_split cs with
      | (?pre, CB ?n (le4 ?w ++ ?l)) => apply (rw_cells_CB_le4 sg m A pre n w l) in H; cbn [app length] in H
      | (?pre, CB ?n (le8 ?w ++ ?l)) => apply (rw_cells_CB_le8 sg m A pre n w l) in H; cbn [app length] in H
      | (?pre, CB ?n (@nil _)) => apply (rw_cells_CB_nil sg m A pre n) in H; cbn [app] in H
      end
  end.


(* [comment removed for export] *)
Ltac lx_aevt_facts :=
  lazymatch goal with
  | |- aevtA ?sg ?K _ _ =>
      lazymatch goal with
      | _ : kinv_laws _ _ K |- _ => idtac
      | |- _ =>
          lazymatch K with
          | KF _ ?R ?HIA ?h ?mo0 => pose proof (KF_kinv sg R HIA h mo0); pose proof (AIh_laws sg R HIA h)
          | HK _ ?R ?HIA ?h => pose proof (AIh_kinv sg R HIA h); pose proof (AIh_laws sg R HIA h)
          | _ => idtac
          end
      end
  | |- _ => idtac
  end.
(* [comment removed for export] *)
Ltac lx_wdecl_note :=
  try (lazymatch goal with
       | MU : munch ?W ?m ?m |- _ =>
           lazymatch goal with
           | _ : lx_wdecl (munch W m m) |- _ => idtac
           | |- _ => repeat match goal with D : lx_wdecl _ |- _ => clear D end; pose proof (MU : lx_wdecl (munch W m m))
           end
       end).
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lx_goal_cs :=
  lazymatch goal with
  | |- evtA _ _ ?CS _ _ => CS
  | |- aevtA _ ?K _ _ => lazymatch goal with _ : kinv_laws _ ?CS K |- _ => CS end
  end.
(* [comment removed for export] *)
Ltac lx_cs_lift :=
  first [
    let CS := lx_goal_cs in
    repeat match goal with
    | H : crange ?CS0 ?a ?n |- _ =>
        lazymatch CS0 with
        | CS => fail
        | _ => lazymatch goal with
               | M : forall x, CS0 x -> CS x |- _ =>
                   first [ lazymatch goal with _ : crange CS a n |- _ => idtac end
                         | pose proof (ALazy.crange_mono CS0 CS a n M H) ];
                   lx_hide1 H
               end
        end
    | H : aobj ?sg ?AL ?CS0 ?m ?a ?n |- _ =>
        lazymatch CS0 with
        | CS => fail
        | _ => lazymatch goal with
               | M : forall x, CS0 x -> CS x |- _ =>
                   first [ lazymatch goal with _ : aobj sg AL CS m a n |- _ => idtac end
                         | pose proof (aobj_cs_mono sg AL CS0 CS m a n M H) ];
                   lx_hide1 H
               end
        end
    end
  | idtac ].
(* [comment removed for export] *)
Definition lx_natd (P : Prop) : Prop := P.
Ltac lx_nat_closed n := lazymatch n with O => idtac | S ?k => lx_nat_closed k end.
(* [comment removed for export] *)
Ltac lx_nat_norm :=
  repeat match goal with
  | H : context [Z.of_nat ?n] |- _ => lx_nat_closed n; let v := eval cbv in (Z.of_nat n) in change (Z.of_nat n) with v in H
  | |- context [Z.of_nat ?n] => lx_nat_closed n; let v := eval cbv in (Z.of_nat n) in change (Z.of_nat n) with v
  end.
Ltac lx_nat_new P := let X := fresh "lxHn" in pose proof P as X; lx_nat_norm; lx_clear_if_dup X.
Ltac lx_nat_facts :=
  lx_nat_norm;
  repeat match goal with
  | H : (?a <= ?b <= ?c)%nat |- _ =>
      lazymatch type of H with lx_natd _ => fail | ?T =>
        lx_nat_new (proj1 (Nat2Z.inj_le a b) (proj1 H)); lx_nat_new (proj1 (Nat2Z.inj_le b c) (proj2 H)); change (lx_natd T) in H end
  | H : (?a <= ?b < ?c)%nat |- _ =>
      lazymatch type of H with lx_natd _ => fail | ?T =>
        lx_nat_new (proj1 (Nat2Z.inj_le a b) (proj1 H)); lx_nat_new (proj1 (Nat2Z.inj_lt b c) (proj2 H)); change (lx_natd T) in H end
  | H : (?a <= ?b)%nat |- _ =>
      lazymatch type of H with lx_natd _ => fail | ?T => lx_nat_new (proj1 (Nat2Z.inj_le a b) H); change (lx_natd T) in H end
  | H : (?a < ?b)%nat |- _ =>
      lazymatch type of H with lx_natd _ => fail | ?T => lx_nat_new (proj1 (Nat2Z.inj_lt a b) H); change (lx_natd T) in H end
  end;
  (* [comment removed for export] *)
  repeat match goal with H : lx_natd ?T |- _ => change T in H end;
  repeat match goal with
  | _ : context [Z.of_nat ?j] |- _ =>
      is_var j; lazymatch goal with _ : 0 <= Z.of_nat j |- _ => fail | |- _ => pose proof (Nat2Z.is_nonneg j) end
  | |- context [Z.of_nat ?j] =>
      is_var j; lazymatch goal with _ : 0 <= Z.of_nat j |- _ => fail | |- _ => pose proof (Nat2Z.is_nonneg j) end
  end.
(* [comment removed for export] *)
Ltac lx_csok_fact :=
  first [ let CS := lx_goal_cs in
          first [ lazymatch goal with H : cs_ok _ CS |- _ => idtac end
                | lazymatch CS with hcs ?segs ?R ?HIA ?h =>
                    let C := fresh "lxCSOK" in pose proof (hcs_ok segs R HIA h) as C;
                    first [ lazymatch goal with _ : 0 <= al_sb _ < _ |- _ => idtac end | pose proof (cs_ok_sb _ _ C) ] end
                | idtac ]
        | lazymatch goal with H : cs_ok _ _ |- _ => idtac end
        | lazymatch goal with |- evtA ?segs _ (hcs _ ?R ?HIA ?h) _ _ => pose proof (hcs_ok segs R HIA h) end
        | idtac ].
Ltac lx_pre :=
  lx_pins_hook;
  lx_aevt_facts; lx_cells_unfold; lx_cb_words; lx_cells_norm; lx_max_facts; lx_imp_disj; lx_frsh_facts; lx_ceil_fact;
  first [ lazymatch goal with H : al_wf _ |- _ => idtac end
        | lazymatch goal with HIA : artA ?segs ?R |- _ => pose proof (art_alwf segs R HIA) end
        | idtac ];
  lx_csok_fact; lx_cs_lift; lx_nat_facts; lx_wdecl_note.

(* [comment removed for export] *)
Ltac lx_rw_merge :=
  let mx := lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => mx end in
  repeat match goal with
  | H1 : rw_cells ?sg mx ?A ?cs1, H2 : rw_cells ?sg' mx ?B ?cs2 |- _ =>
      lazymatch cs1 with cons _ _ => idtac end; lazymatch cs2 with cons _ _ => idtac end;
      (* [comment removed for export] *)
      lazymatch cs1 with context [CB _ _] => fail | _ => idtac end; lazymatch cs2 with context [CB _ _] => fail | _ => idtac end;
      let n := eval cbv in (Z.of_nat (cells_size cs1)) in
      let d := addr_diff B A in constr_eq d n;
      let J := fresh "Hrw" in let H2' := fresh "Hrw" in
      assert (H2' : rw_cells sg mx (A + Z.of_nat (cells_size cs1)) cs2)
        by (replace (A + Z.of_nat (cells_size cs1)) with B
              by (cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; clear; lia);
            exact H2);
      pose proof (proj2 (rw_cells_app sg mx A cs1 cs2) (conj H1 H2')) as J;
      cbn [app] in J; clear H1 H2 H2'; rename J into H1
  end.

(* [comment removed for export] *)
Ltac lx_split_CB A sizes :=
  match goal with H : rw_cells ?sg ?m A [CB ?n ?j] |- _ =>
    apply (rw_cells_split_CB sg m A [] n j [] sizes) in H; [| reflexivity]; cbn [mk_CB_cells app sum_nat] in H end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lx_cur_mem := lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => mx end.

(* [comment removed for export] *)
Ltac lx_clear_stale_at m0 mx :=
  repeat match goal with
         | H : rw_cells _ m0 _ _ |- _ => clear H
         | H : ro_cells _ m0 _ _ |- _ => clear H
         | H : bytes_at _ m0 _ _ |- _ => clear H
         | H : stk _ m0 _ _ |- _ => clear H
         | H : aobj _ _ _ m0 _ _ |- _ => clear H
         | H : mem_inv _ m0 |- _ => clear H
         end.
Ltac lx_clear_stale mx :=
  try (lazymatch goal with M : munch _ ?m0 mx |- _ => lazymatch m0 with mx => idtac | _ => lx_clear_stale_at m0 mx end end);
  try (lazymatch goal with M : wmono _ ?m0 mx |- _ => lazymatch m0 with mx => idtac | _ => lx_clear_stale_at m0 mx end end).
(* [comment removed for export] *)
Ltac lx_drop_stale_all mx :=
  repeat match goal with
         | H : rw_cells _ ?m0 _ _ |- _ => lazymatch m0 with mx => fail | _ => clear H end
         | H : ro_cells _ ?m0 _ _ |- _ => lazymatch m0 with mx => fail | _ => clear H end
         | H : bytes_at _ ?m0 _ _ |- _ => lazymatch m0 with mx => fail | _ => clear H end
         | H : stk _ ?m0 _ _ |- _ => lazymatch m0 with mx => fail | _ => clear H end
         | H : aobj _ _ _ ?m0 _ _ |- _ => lazymatch m0 with mx => fail | _ => clear H end
         | H : mem_inv _ ?m0 |- _ => lazymatch m0 with mx => fail | _ => clear H end
         end.
(* [comment removed for export] *)
Ltac lx_stale_hook mx := lx_drop_stale_all mx.

(* [comment removed for export] *)
Ltac lx_call_prep :=
  let mx := lx_cur_mem in
  (* [comment removed for export] *)
  try match goal with HH : HM ?segs ?R ?HIA ?h ?LB ?LF ?m0, MU : munch ?W ?m0 mx, WM : wmono _ ?m0 mx |- _ =>
        lazymatch m0 with mx => fail | _ =>
        lazymatch goal with _ : HM segs R HIA h LB LF mx |- _ => fail | _ =>
        let HHc := fresh "HHc" in pose proof HH as HHc;
        apply (hm_munch segs R HIA h LB LF W m0 mx) in HHc; [| exact MU | exact WM | solve_w_writable] end end end;
  (* [comment removed for export] *)
  try match goal with AB : abase ?segs ?L ?m0, MU : munch ?W ?m0' mx, OK : cs_ok ?L' ?CS |- _ =>
        lazymatch m0 with mx => fail | _ =>
        apply (abase_munch segs L CS OK W m0 mx) in AB; [| solve_w_client | solve_w_nonempty | exact MU] end end;
  lx_stale_hook mx.

(* [comment removed for export] *)
Tactic Notation "lx_rn_rw" ident(N) constr(a) :=
  let mx := lx_cur_mem in match goal with H : rw_cells _ mx a _ |- _ => rename H into N end.
Tactic Notation "lx_rn_ro" ident(N) constr(a) :=
  let mx := lx_cur_mem in match goal with H : ro_cells _ mx a _ |- _ => rename H into N end.
Tactic Notation "lx_rn_by" ident(N) constr(a) :=
  let mx := lx_cur_mem in match goal with H : bytes_at _ mx a _ |- _ => rename H into N end.
Tactic Notation "lx_rn_aobj" ident(N) constr(a) :=
  let mx := lx_cur_mem in match goal with H : aobj _ _ _ mx a _ |- _ => rename H into N end.
Tactic Notation "lx_rn_stk" ident(N) :=
  let mx := lx_cur_mem in match goal with H : stk _ mx _ _ |- _ => rename H into N end.
Tactic Notation "lx_rn_hm" ident(N) :=
  let mx := lx_cur_mem in match goal with H : HM _ _ _ _ _ _ mx |- _ => rename H into N end.


(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lx_rejoin :=
  let mx := lx_cur_mem in
  repeat match goal with
  | H1 : rw_cells ?sg mx ?A ?pre, H2 : rw_cells _ mx ?B ?post |- _ =>
      let z := eval cbv in (Z.of_nat (cells_size pre)) in
      replace B with (A + z) in H2 by (clear; lia);
      let J := fresh "J" in
      pose proof (proj2 (rw_cells_app sg mx A pre post) (conj H1 ltac:(change (Z.of_nat (cells_size pre)) with z; exact H2))) as J;
      clear H1 H2; cbn [app] in J
  end.
(* [comment removed for export] *)
Tactic Notation "lx_wcell" ident(X) :=
  repeat match goal with
         | H : rw_cells _ _ _ ?cs |- _ => lazymatch cs with context [C8 X] => rewrite <- (Z_to_bv_bv_unsigned X) in H end
         end.

(* [comment removed for export] *)
Tactic Notation "lx_r0" ident(r) := let R := fresh "R0" in assert (R : r = 0) by lx_arith.
(* [comment removed for export] *)
Tactic Notation "lx_r0s" ident(r) := let R := fresh "R0" in assert (R : r = 0) by lx_arith; subst r.

(* [comment removed for export] *)
Ltac lx_eqsubst := repeat match goal with H : ?x = _ |- _ => is_var x; lazymatch type of x with bv _ => subst x end end.
(* [comment removed for export] *)
Ltac lx_cells_upto cs d :=
  lazymatch eval vm_compute in (Z.eqb d 0) with
  | true => constr:(0%nat)
  | false =>
      lazymatch cs with
      | cons ?c ?cs' =>
          let z := eval cbv in (Z.of_nat (csize c)) in
          let d' := eval vm_compute in (d - z)%Z in
          lazymatch eval vm_compute in (Z.leb 0 d') with
          | true => let k := lx_cells_upto cs' d' in constr:(S k)
          end
      end
  end.
(* [comment removed for export] *)
Ltac lx_resplit :=
  let mx := lx_cur_mem in
  repeat match goal with
  | H0 : rw_cells ?sg ?m0 ?A0 _, H : rw_cells ?sg' mx ?A ?cs |- _ =>
      lazymatch m0 with mx => fail | _ =>
        lazymatch goal with
        | _ : rw_cells _ mx A0 _ |- _ => fail
        | _ => let d := addr_diff A0 A in
               lazymatch eval vm_compute in (Z.ltb 0 d) with
               | true => let k := lx_cells_upto cs d in
                         let H2 := fresh "Hspl" in chunk_split H k H H2;
                         lazymatch type of H2 with rw_cells _ _ ?A2 _ => replace A2 with A0 in H2 by (clear; lia) end
               end
        end
      end
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lx_ivl_list_eq := repeat first [ reflexivity | apply (f_equal2 (@cons _)) | apply (f_equal2 (@pair _ _)) | (clear; lia) ].
Ltac lx_munch_respell :=
  try (lazymatch goal with
       | D : lx_wdecl (munch ?W ?m0 _), H : munch ?W2 ?m0' ?mx |- _ =>
           lazymatch W2 with
           | W => idtac
           | _ => let E := fresh in assert (E : W2 = W) by (clear; lx_ivl_list_eq); rewrite E in H; clear E
           end
       end).
(* [comment removed for export] *)
Ltac lx_carry_from m0 mx :=
  repeat match goal with
  | H : rw_cells ?sg mx ?a _, H0 : rw_cells ?sg m0 ?a _ |- _ => clear H0; rename H into H0
  | H : ro_cells ?sg mx ?a _, H0 : ro_cells ?sg m0 ?a _ |- _ => clear H0; rename H into H0
  | H : bytes_at ?sg mx ?a ?bs, H0 : bytes_at ?sg m0 ?a ?bs |- _ => clear H0; rename H into H0
  | H : stk ?sg mx ?lo ?hi, H0 : stk ?sg m0 ?lo ?hi |- _ => clear H0; rename H into H0
  | H : aobj ?sg ?al ?cs mx ?a ?n, H0 : aobj ?sg ?al ?cs m0 ?a ?n |- _ => clear H0; rename H into H0
  | H : mem_inv ?sg mx, H0 : mem_inv ?sg m0 |- _ => clear H0; rename H into H0
  | H : abase ?sg ?al mx, H0 : abase ?sg ?al m0 |- _ => clear H0; rename H into H0
  end.
(* [comment removed for export] *)
Ltac lx_carry_generic mx :=
  repeat match goal with
  | H : rw_cells ?sg mx ?a _, H0 : rw_cells ?sg ?m0 ?a _ |- _ =>
      lazymatch m0 with mx => fail | _ => clear H0; rename H into H0 end
  | H : ro_cells ?sg mx ?a _, H0 : ro_cells ?sg ?m0 ?a _ |- _ =>
      lazymatch m0 with mx => fail | _ => clear H0; rename H into H0 end
  | H : bytes_at ?sg mx ?a ?bs, H0 : bytes_at ?sg ?m0 ?a ?bs |- _ =>
      lazymatch m0 with mx => fail | _ => clear H0; rename H into H0 end
  | H : stk ?sg mx ?lo ?hi, H0 : stk ?sg ?m0 ?lo ?hi |- _ =>
      lazymatch m0 with mx => fail | _ => clear H0; rename H into H0 end
  | H : aobj ?sg ?al ?cs mx ?a ?n, H0 : aobj ?sg ?al ?cs ?m0 ?a ?n |- _ =>
      lazymatch m0 with mx => fail | _ => clear H0; rename H into H0 end
  | H : mem_inv ?sg mx, H0 : mem_inv ?sg ?m0 |- _ =>
      lazymatch m0 with mx => fail | _ => clear H0; rename H into H0 end
  | H : abase ?sg ?al mx, H0 : abase ?sg ?al ?m0 |- _ =>
      lazymatch m0 with mx => fail | _ => clear H0; rename H into H0 end
  end.
(* [comment removed for export] *)
Ltac lx_carry_munch_first mx :=
  first [ lazymatch goal with M : munch _ ?m0 mx |- _ => lazymatch m0 with mx => fail | _ => lx_carry_from m0 mx end end
        | lx_carry_generic mx ].
Ltac lx_carry_names mx := lx_carry_generic mx.
Ltac lx_carry :=
  let mx := lx_cur_mem in
  lx_munch_respell;
  try lx_resplit;
  lx_carry_names mx;
  lx_stale_hook mx.   (* [comment removed for export] *)
