(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage2_defs Sj_stage2_traps Sj_stage2_guard Sj_tables Sj_stage2_hooks Sj_stage2_auto Sj_stage2_wkit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_buf | s2_load_esc | s2_load_dig | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].

Section StrCm.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Notation bs := (e_bs E).

  Section Loop.
    Variables (Q : machine_state -> Prop) (dpt t40 i48 sbv r9 : Z) (sc : list (bool * Z)).
    Hypothesis KX : exit_k E Q.
    Hypothesis HGS : (Z.of_nat (length (e_sbs E)) = sbv)%Z.
    Notation SLOTS j0 j8 j16 j24 j72 := ([CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; C8 (Z_to_bv 64 (dpt)); C8 (Z_to_bv 64 (t40)); C8 (Z_to_bv 64 (i48)); C8 (Z_to_bv 64 (e_SBUF E + sbv)); C8 (Z_to_bv 64 (e_THIS E)); CB 8 j72]).

    Definition headk (p d : Z) : Prop :=
      forall xs0 xs1 xa0 xa1 xs6 xt3 xt5 j0 j8 j16 j24 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
        MEMI E (e_nxt0 E) (SLOTS j0 j8 j16 j24 j72) sc fc m1 ->
        evt usegs Q (S2R E 0x4af5c (Z_to_bv 64 (23669)) (Z_to_bv 64 ((-3))) (Z_to_bv 64 ((-4))) (Z_to_bv 64 (4)) xs0 xs1 xa0 xa1 (Z_to_bv 64 ((-1))) (Z_to_bv 64 (92)) (Z_to_bv 64 (2)) (Z_to_bv 64 (e_SBUF E + sbv + 4 + d)) (Z_to_bv 64 (117)) (Z_to_bv 64 ((-2))) (Z_to_bv 64 (56320)) (Z_to_bv 64 (e_SBUF E + sbv + 4)) (Z_to_bv 64 (e_BUF E + p)) (Z_to_bv 64 (e_BUF E)) xs6 (Z_to_bv 64 (18446744073709467439)) (Z_to_bv 64 ((-56320))) (Z_to_bv 64 (r9)) (Z_to_bv 64 (84176)) (Z_to_bv 64 (55296)) xt3 (Z_to_bv 64 (34)) xt5 (Z_to_bv 64 (127)) F fc m1).

    Lemma strc_mb1 : forall p d v xs0 xs1 xa0 xa1 xs4 xt3 j0 j8 j16 j24 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      (0 <= sbv /\ 0 <= d /\ sbv + 4 + d + 4 <= e_scap E)%Z -> (0 <= p <= e_len E + 64)%Z ->
      MEMI E (e_nxt0 E) (SLOTS j0 j8 j16 j24 j72) sc fc m1 ->
      headk p (d + 1) ->
      evt usegs Q (S2R E 0x4b14c (Z_to_bv 64 (23669)) (Z_to_bv 64 ((-3))) (Z_to_bv 64 ((-4))) (Z_to_bv 64 (4)) xs0 xs1 xa0 xa1 (Z_to_bv 64 ((-1))) (Z_to_bv 64 (92)) (Z_to_bv 64 (2)) (Z_to_bv 64 (e_SBUF E + sbv + 4 + d)) (Z_to_bv 64 (117)) (Z_to_bv 64 ((-2))) (Z_to_bv 64 (56320)) (Z_to_bv 64 (e_SBUF E + sbv + 4)) xs4 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_BUF E + p)) (Z_to_bv 64 (18446744073709467439)) (Z_to_bv 64 ((-56320))) (Z_to_bv 64 (r9)) (Z_to_bv 64 (84176)) (Z_to_bv 64 (55296)) xt3 (Z_to_bv 64 (34)) (Z_to_bv 64 (v)) (Z_to_bv 64 (127)) F fc m1).
    Proof using OK KX HGS.
      intros p d v xs0 xs1 xa0 xa1 xs4 xt3 j0 j8 j16 j24 j72 F fc m1 HR HP HM KH.
      s2_env OK.
      pose proof HM as HMo. s2_open_mem HMo.
      wrun_to 0x4af5c%Z.
      replace (e_SBUF E + sbv + 4 + d + 1)%Z with (e_SBUF E + sbv + 4 + (d + 1))%Z by lia.
      eapply KH. eassumption.
    Qed.

    Lemma strc_mb : forall p d v xs0 xs1 xa1 xs4 xt3 j0 j8 j16 j24 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      (0 <= sbv /\ 0 <= d /\ sbv + 4 + d + 4 <= e_scap E)%Z -> (0 <= p <= e_len E + 64)%Z ->
      MEMI E (e_nxt0 E) (SLOTS j0 j8 j16 j24 j72) sc fc m1 ->
      headk p (d + 2) -> headk p (d + 3) -> headk p (d + 4) ->
      evt usegs Q (S2R E 0x4b158 (Z_to_bv 64 (23669)) (Z_to_bv 64 ((-3))) (Z_to_bv 64 ((-4))) (Z_to_bv 64 (4)) xs0 xs1 (Z_to_bv 64 (5)) xa1 (Z_to_bv 64 ((-1))) (Z_to_bv 64 (92)) (Z_to_bv 64 (2)) (Z_to_bv 64 (e_SBUF E + sbv + 4 + d)) (Z_to_bv 64 (117)) (Z_to_bv 64 ((-2))) (Z_to_bv 64 (56320)) (Z_to_bv 64 (e_SBUF E + sbv + 4)) xs4 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_BUF E + p)) (Z_to_bv 64 (18446744073709467439)) (Z_to_bv 64 ((-56320))) (Z_to_bv 64 (r9)) (Z_to_bv 64 (84176)) (Z_to_bv 64 (55296)) xt3 (Z_to_bv 64 (34)) (Z_to_bv 64 (v)) (Z_to_bv 64 (127)) F fc m1).
    Proof using OK KX HGS.
      intros p d v xs0 xs1 xa1 xs4 xt3 j0 j8 j16 j24 j72 F fc m1 HR HP HM KH2 KH3 KH4.
      s2_env OK.
      pose proof HM as HMo. s2_open_mem HMo.

      let fin := fun _ => (lazymatch goal with
                  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
                      lazymatch pc with
                      | 0x4bfd0%Z => eapply (KX 5%Z); [s2_errlit|]; s2_close_memx
                      | 0x4af5c%Z =>
                          first [ replace (e_SBUF E + sbv + 4 + d + 2)%Z with (e_SBUF E + sbv + 4 + (d + 2))%Z by lia; eapply KH2; eassumption
                                | replace (e_SBUF E + sbv + 4 + d + 3)%Z with (e_SBUF E + sbv + 4 + (d + 3))%Z by lia; eapply KH3; eassumption
                                | replace (e_SBUF E + sbv + 4 + d + 4)%Z with (e_SBUF E + sbv + 4 + (d + 4))%Z by lia; eapply KH4; eassumption ]
                      end
                  end) in
      let rec go _ := (repeat (lazymatch goal with
                               | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
                                   lazymatch pc with 0x4af5c%Z => fail | 0x4bfd0%Z => fail | _ => idtac end
                               | _ => idtac end;
                               first [ gguard | wstep ]);
                       first [ fin tt | (let KB := fresh "KB" in if_cases KB; clear KB; go tt) ]) in
      go tt.
    Qed.

    Lemma strc_mb0s : forall p d v xs0 xs1 xa1 xs4 xt3 j0 j8 j16 j24 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      (0 <= sbv /\ 0 <= d /\ sbv + 4 + d + 4 <= e_scap E)%Z -> (0 <= p <= e_len E + 64)%Z ->
      MEMI E (e_nxt0 E) (SLOTS j0 j8 j16 j24 j72) sc fc m1 ->
      (forall w, (1 <= w <= 4)%Z -> headk p (d + w)) ->
      evt usegs Q (S2R E 0x4b148 (Z_to_bv 64 (23669)) (Z_to_bv 64 ((-3))) (Z_to_bv 64 ((-4))) (Z_to_bv 64 (4)) xs0 xs1 (Z_to_bv 64 (5)) xa1 (Z_to_bv 64 ((-1))) (Z_to_bv 64 (92)) (Z_to_bv 64 (2)) (Z_to_bv 64 (e_SBUF E + sbv + 4 + d)) (Z_to_bv 64 (117)) (Z_to_bv 64 ((-2))) (Z_to_bv 64 (56320)) (Z_to_bv 64 (e_SBUF E + sbv + 4)) xs4 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_BUF E + p)) (Z_to_bv 64 (18446744073709467439)) (Z_to_bv 64 ((-56320))) (Z_to_bv 64 (r9)) (Z_to_bv 64 (84176)) (Z_to_bv 64 (55296)) xt3 (Z_to_bv 64 (34)) (Z_to_bv 64 (v)) (Z_to_bv 64 (127)) F fc m1).
    Proof using OK KX HGS.
      intros p d v xs0 xs1 xa1 xs4 xt3 j0 j8 j16 j24 j72 F fc m1 HR HP HM KH.
      zstep.
      let KB := fresh "KB" in if_cases KB; clear KB;
      first [ eapply (strc_mb1 p d); [exact HR | exact HP | exact HM | apply KH; lia]
            | eapply (strc_mb p d); [exact HR | exact HP | exact HM | apply KH; lia | apply KH; lia | apply KH; lia] ].
    Qed.

  End Loop.
End StrCm.
