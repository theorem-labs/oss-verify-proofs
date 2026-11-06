(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import ImageA.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import RzCPS StoreFast.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import Layout.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma LIB0_write : forall (m : mem) a bs (n : Z), Z.of_nat (length bs) = n -> 0 <= a -> a + n <= 2^64 ->
  LIB0 m -> (a + n <= 0xd0400 \/ 0xd0468 <= a) -> LIB0 (write_to_mem m (wa a) bs).
Proof.
  intros m a bs n Hn Ha Hl (H1 & H2 & H3) Hd. unfold LIB0, g_LeptMsgSeverity, g_pix_alloc, g_pix_dealloc in *.
  split; [| split]; (eapply rw_cells_frame_n; [exact Hn| exact Ha| exact Hl| eassumption| cbn [cells_size csize Nat.add]; lia]).
Qed.
Lemma LIBH_write : forall (m : mem) a bs (n : Z), Z.of_nat (length bs) = n -> 0 <= a -> a + n <= 2^64 ->
  LIBH m -> (a + n <= 0xd0400 \/ 0xd0468 <= a) -> LIBH (write_to_mem m (wa a) bs).
Proof.
  intros m a bs n Hn Ha Hl (H0 & H1) Hd. split; [exact (LIB0_write m a bs n Hn Ha Hl H0 Hd)|].
  unfold g_stderr_handler in *. eapply rw_cells_frame_n; [exact Hn| exact Ha| exact Hl| eassumption| cbn [cells_size csize Nat.add]; lia].
Qed.
(* [comment removed for export] *)
Lemma io_ssp_write : forall (m : mem) a bs (n : Z), Z.of_nat (length bs) = n -> 0 <= a -> a + n <= 2^64 ->
  io_ssp m -> (a + n <= 0x10000 \/ SEGTOP_A <= a \/ (0xd0400 <= a /\ a + n <= 0xd0468)) -> io_ssp (write_to_mem m (wa a) bs).
Proof.
  intros m a bs n Hn Ha Hl (g & H1 & H2) Hd. exists g. unfold SEGTOP_A in Hd.
  split; (eapply ro_cells_frame_n; [exact Hn| exact Ha| exact Hl| eassumption| cbn [cells_size csize Nat.add]; lia]).
Qed.

Ltac lept_transport_extra3 m a bs n Hn Ha Hl :=
  lept_transport_extra2 m a bs n Hn Ha Hl;
  repeat match goal with
  | H : LIBH m |- _ =>
      first [ apply (LIBH_write m a bs n Hn Ha Hl) in H; [ | tlia ]
            | idtac "note: dropping LIBH (store may hit the library statics)"; clear H ]
  | H : io_ssp m |- _ =>
      first [ apply (io_ssp_write m a bs n Hn Ha Hl) in H; [ | unfold SEGTOP_A; tlia ]
            | idtac "note: dropping io_ssp"; clear H ]
  end.
Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= lept_transport_extra3 m a bs n Hn Ha Hl.

(* [comment removed for export] *)
Section Env.
Variable RT : rt_sig.
Hypothesis GP : rt_gaps RT.

Lemma static_agree : forall (P : Z -> Prop) (m m' : mem), agree_on P m m' -> (forall a, client_static a -> P a) ->
  forall lo n, In (lo, n) LEPT_GLOBALS -> agree_on (fun x => lo <= x < lo + n) m m'.
Proof using GP.
  intros P m m' AG HP lo n Hin. eapply agree_sub; [exact AG|]. cbv beta. intros x Hx. apply HP.
  apply (gp_globals_client RT GP). exists lo, (lo + n). split; [| exact Hx].
  unfold LEPT_GLOBALS in *. cbn [map fst snd In] in *. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; tauto|]). destruct Hin.
Qed.

Lemma LIBH_agree : forall (P : Z -> Prop) (m m' : mem), LIBH m -> agree_on P m m' -> (forall a, client_static a -> P a) -> LIBH m'.
Proof using GP.
  intros P m m' ((H1 & H2 & H3) & H4) AG HP. unfold LIBH, LIB0, g_LeptMsgSeverity, g_pix_alloc, g_pix_dealloc, g_stderr_handler in *.
  split; [split; [| split]|].
  - apply (rw_cells_agree_nw asegs m m' _ _ H1). exact (static_agree P m m' AG HP 0xd0400 4 ltac:(cbn; tauto)).
  - apply (rw_cells_agree_nw asegs m m' _ _ H2). exact (static_agree P m m' AG HP 0xd0440 8 ltac:(cbn; tauto)).
  - apply (rw_cells_agree_nw asegs m m' _ _ H3). exact (static_agree P m m' AG HP 0xd0460 8 ltac:(cbn; tauto)).
  - apply (rw_cells_agree_nw asegs m m' _ _ H4). exact (static_agree P m m' AG HP 0xd0420 8 ltac:(cbn; tauto)).
Qed.

Lemma io_ssp_agree : forall (P : Z -> Prop) Σ' (m m' : mem), io_ssp m -> ART RT Σ' m' -> agree_on P m m' ->
  (forall a, client_static a -> P a) -> io_ssp m'.
Proof using GP.
  intros P Σ' m m' H HA AG HP. apply (gp_ssp_keep RT GP Σ' m m' H HA). intros a Ha. exact (AG a (HP _ Ha)).
Qed.
End Env.

(* [comment removed for export] *)
Ltac static_in_P :=
  let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
  first [ right; left; exact Ha
        | split; [ right; left; exact Ha
                 | first [ cbn [outside]; exact I
                         | let Hc := fresh in intros Hc;
                           pose proof (client_static_below a Ha); pose proof (client_static_ge a Ha); unfold SEGTOP_A in *; first [ lia | tlia ]
                         | cbn [outside]; pose proof (client_static_below a Ha); pose proof (client_static_ge a Ha);
                           unfold SEGTOP_A in *; repeat split; tlia ] ] ].

Ltac lept_rt_transport_extra m m' AG :=
  repeat match goal with
  | H : LIBH m |- _ =>
      first [ lazymatch goal with _ : LIBH m' |- _ => clear H end
            | match goal with GP : rt_gaps ?RT |- _ => apply (fun h => LIBH_agree RT GP _ m m' h AG ltac:(static_in_P)) in H end
            | idtac "note: dropping LIBH at a runtime call"; clear H ]
  | H : io_ssp m |- _ =>
      first [ lazymatch goal with _ : io_ssp m' |- _ => clear H end
            | match goal with GP : rt_gaps ?RT, A : ART ?RT ?S m' |- _ =>
                apply (fun h => io_ssp_agree RT GP _ S m m' h A AG ltac:(static_in_P)) in H end
            | idtac "note: dropping io_ssp at a runtime call"; clear H ]
  end.
Ltac rt_transport_extra m m' AG ::= lept_rt_transport_extra m m' AG.

(* [comment removed for export] *)
Ltac lib_load_step :=
  next_instr ltac:(fun i =>
    lazymatch i with
    | Load _ _ _ ?rs ?imm =>
        reg_val rs ltac:(fun v =>
          lazymatch v with
          | Z_to_bv 64 ?E =>
              is_Zlit E;
              let a := eval vm_compute in (E + bv_signed imm)%Z in
              let inb := eval vm_compute in (existsb (fun r => (fst r <=? a) && (a <? fst r + snd r))%Z LEPT_GLOBALS) in
              lazymatch inb with
              | true =>
                  lazymatch goal with
                  | LH : LIBH ?m |- _ =>
                      let C1 := fresh "LC" in let C2 := fresh "LC" in let C3 := fresh "LC" in let C4 := fresh "LC" in
                      pose proof LH as ((C1 & C2 & C3) & C4);
                      unfold g_LeptMsgSeverity, g_pix_alloc, g_pix_dealloc, g_stderr_handler, e_devnull, e_malloc, e_free in C1, C2, C3, C4;
                      lstep; clear C1 C2 C3 C4
                  end
              end
          end)
    end).
Ltac special_step ::= lib_load_step.

(* [comment removed for export] *)
Ltac lib_refresh RT GP :=
  lazymatch goal with
  | |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?m' _))) _ =>
      lazymatch goal with
      | A : ART RT S m' |- _ =>
          let G := fresh "GSEV" in
          pose proof (gp_got_lib RT GP S m' A) as G; unfold g_GOT_LeptMsgSeverity in G;
          let AG := fresh "ACCG" in
          pose proof (gp_acc_globals RT GP S m' A) as AG; unfold LEPT_GLOBALS in AG;
          apply Forall_inv in AG; cbn [fst snd] in AG
      end
  end.

(* [comment removed for export] *)
Ltac lit_in := eexists; unfold LEPT_LITS; repeat first [ left; reflexivity | right ].
Ltac lenv_tac :=
  unfold lenv, LSTK, STDERR_STACK; rewrite ?unsigned_lit by lia;
  split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|];
  repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end;
  repeat split; ul.
Ltac lres_tac :=
  unfold lres; repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end;
  repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end;
  cbn [length]; unfold FRAMES_MAX, LIVE_MAX in *;
  repeat lazymatch goal with |- _ /\ _ => split end;
  lazymatch goal with
  | |- forall p n, In _ _ -> _ =>
      let p := fresh "p" in let n := fresh "n" in let H := fresh "H" in intros p n H; cbn [In] in H;
      repeat (destruct H as [H|H]; [injection H as <- <-; lia|]); eauto
  | |- _ => first [ lia | assumption
                  | unfold mcost in *; repeat match goal with _ : context [if ?c then _ else _] |- _ => destruct c end; lia ]
  end.
(* [comment removed for export] *)
Ltac alg_tac :=
  repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end;
  repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end;
  repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end;
  repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end;
  repeat split;
  first [ reflexivity | lia | solve [auto]
        | unfold mcost in *; repeat match goal with _ : context [if ?c then _ else _] |- _ => destruct c end;
          repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia
        | lazymatch goal with |- ?g => idtac "alg_tac leaves:" g end ].

Ltac after_call_unfold ::=
  unfold lpost, lpost_f, keeps, keepsL, rsize in *;
  cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data c_arr c_depth c_nalloc c_n] in *.

(* [comment removed for export] *)
Ltac ul ::= unfold STDERR_STACK, LSTK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, LIVE_MAX in *; lia.
