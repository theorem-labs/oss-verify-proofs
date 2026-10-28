(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_akit Sj_stage2_defs Sj_stage2_traps Sj_stage2_guard Sj_tables Sj_stage2_hooks Sj_stage2_strkit Sj_stage2_auto Sj_stage2_wkit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_shadow | s2_load_shadow_dig | s2_load_buf | s2_load_esc | s2_load_dig | s2_load_dig2 | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].

Section StrRm.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Notation bs := (e_bs E).

  Section Loop.
    Variables (Q : machine_state -> Prop) (dpt t40 i48 sbv r9 : Z) (sc : list (bool * Z)).
    Hypothesis KX : exit_k E Q.
    Hypothesis HGS : (Z.of_nat (length (e_sbs E)) = sbv)%Z.
    Notation SLOTS j64 j72 j80 j88 j96 j104 j112 j272 := ([CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; C8 (Z_to_bv 64 (e_SBUF E + sbv + 4)); C8 (Z_to_bv 64 (18446744073709495296)); C8 (Z_to_bv 64 (23669)); C8 (Z_to_bv 64 (56320)); C8 (Z_to_bv 64 (55296)); C8 (Z_to_bv 64 (i48)); C8 (Z_to_bv 64 (t40)); C8 (Z_to_bv 64 (e_SBUF E + sbv)); CB 8 j272]).

    Definition headk (p d : Z) : Prop :=
      forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa6 xa7 xs6 xs7 xs10 xt3 xt4 xt5 xt6 j64 j72 j80 j88 j96 j104 j112 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
        MEMI E (e_nxt0 E) (SLOTS j64 j72 j80 j88 j96 j104 j112 j272) sc fc m1 ->
        evt asegs Q (S2R E 0xbe0ec xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 (Z_to_bv 64 (34)) xa4 (Z_to_bv 64 (117)) xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (1)) xs6 xs7 (Z_to_bv 64 (92)) (Z_to_bv 64 (e_SBUF E + sbv + 4 + d)) xs10 (Z_to_bv 64 (e_BUF E + p)) xt3 xt4 xt5 xt6 F fc m1).

    Lemma strr_mb1 : forall p d v xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6 j64 j72 j80 j88 j96 j104 j112 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      (0 <= sbv /\ 0 <= d /\ sbv + 4 + d + 4 <= e_scap E)%Z -> (0 <= p <= e_len E + 64)%Z ->
      MEMI E (e_nxt0 E) (SLOTS j64 j72 j80 j88 j96 j104 j112 j272) sc fc m1 ->
      headk p (d + 1) ->
      evt asegs Q (S2R E 0xbe17c xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (e_BUF E + p)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (1)) (Z_to_bv 64 (SHA (e_SBUF E + sbv + 4 + d))) (Z_to_bv 64 (5)) (Z_to_bv 64 (92)) (Z_to_bv 64 (e_SBUF E + sbv + 4 + d)) (Z_to_bv 64 (v)) xs11 xt3 xt4 xt5 xt6 F fc m1).
    Proof using OK SHZ KX HGS.
      intros p d v xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6 j64 j72 j80 j88 j96 j104 j112 j272 F fc m1 HR HP HM KH.
      s2_env OK.
      pose proof HM as HMo. s2_open_mem HMo.
      wrun_to 0xbe0ec%Z.
      replace (e_SBUF E + sbv + 4 + d + 1)%Z with (e_SBUF E + sbv + 4 + (d + 1))%Z by lia.
      eapply KH. eassumption.
    Qed.

    Lemma strr_mb : forall p d v xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6 j64 j72 j80 j88 j96 j104 j112 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      (0 <= sbv /\ 0 <= d /\ sbv + 4 + d + 4 <= e_scap E)%Z -> (0 <= p <= e_len E + 64)%Z ->
      MEMI E (e_nxt0 E) (SLOTS j64 j72 j80 j88 j96 j104 j112 j272) sc fc m1 ->
      headk p (d + 2) -> headk p (d + 3) -> headk p (d + 4) ->
      evt asegs Q (S2R E 0xbe2c0 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (e_BUF E + p)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (1)) (Z_to_bv 64 (SHA (e_SBUF E + sbv + 4 + d))) (Z_to_bv 64 (5)) (Z_to_bv 64 (92)) (Z_to_bv 64 (e_SBUF E + sbv + 4 + d)) (Z_to_bv 64 (v)) xs11 xt3 xt4 xt5 xt6 F fc m1).
    Proof using OK SHZ KX HGS.
      intros p d v xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6 j64 j72 j80 j88 j96 j104 j112 j272 F fc m1 HR HP HM KH2 KH3 KH4.
      s2_env OK.
      pose proof HM as HMo. s2_open_mem HMo.

      let fin := fun _ => (lazymatch goal with
                  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
                      lazymatch pc with
                      | 0xcb1dc%Z => eapply (KX 5%Z); [s2_errlit|]; s2_close_memx
                      | 0xbe0ec%Z =>
                          first [ replace (e_SBUF E + sbv + 4 + d + 2)%Z with (e_SBUF E + sbv + 4 + (d + 2))%Z by lia; eapply KH2; eassumption
                                | replace (e_SBUF E + sbv + 4 + d + 3)%Z with (e_SBUF E + sbv + 4 + (d + 3))%Z by lia; eapply KH3; eassumption
                                | replace (e_SBUF E + sbv + 4 + d + 4)%Z with (e_SBUF E + sbv + 4 + (d + 4))%Z by lia; eapply KH4; eassumption ]
                      end
                  end) in
      let rec go _ := (repeat (lazymatch goal with
                               | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
                                   lazymatch pc with 0xbe0ec%Z => fail | 0xcb1dc%Z => fail | _ => idtac end
                               | _ => idtac end;
                               first [ gguard | wstep ]);
                       first [ fin tt | (let KB := fresh "KB" in if_cases KB; clear KB; go tt) ]) in
      go tt.
    Qed.

    Lemma strr_mb0s : forall p d v xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6 j64 j72 j80 j88 j96 j104 j112 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      (0 <= sbv /\ 0 <= d /\ sbv + 4 + d + 4 <= e_scap E)%Z -> (0 <= p <= e_len E + 64)%Z ->
      MEMI E (e_nxt0 E) (SLOTS j64 j72 j80 j88 j96 j104 j112 j272) sc fc m1 ->
      (forall w, (1 <= w <= 4)%Z -> headk p (d + w)) ->
      evt asegs Q (S2R E 0xbe174 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (e_BUF E + p)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (1)) (Z_to_bv 64 (SHA (e_SBUF E + sbv + 4 + d))) (Z_to_bv 64 (5)) (Z_to_bv 64 (92)) (Z_to_bv 64 (e_SBUF E + sbv + 4 + d)) (Z_to_bv 64 (v)) xs11 xt3 xt4 xt5 xt6 F fc m1).
    Proof using OK SHZ KX HGS.
      intros p d v xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6 j64 j72 j80 j88 j96 j104 j112 j272 F fc m1 HR HP HM KH.
      grun.
      let KB := fresh "KB" in if_cases KB; clear KB;
      first [ eapply (strr_mb1 p d); [exact HR | exact HP | exact HM | apply KH; lia]
            | eapply (strr_mb p d); [exact HR | exact HP | exact HM | apply KH; lia | apply KH; lia | apply KH; lia] ].
    Qed.

    Lemma strr_mb0p : forall p d v xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6 j64 j72 j80 j88 j96 j104 j112 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      (0 <= sbv /\ 0 <= d /\ sbv + 4 + d + 4 <= e_scap E)%Z -> (0 <= p <= e_len E + 64)%Z ->
      MEMI E (e_nxt0 E) (SLOTS j64 j72 j80 j88 j96 j104 j112 j272) sc fc m1 ->
      (forall w, (1 <= w <= 4)%Z -> headk p (d + w)) ->
      evt asegs Q (S2R E 0xbe240 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (e_BUF E + p)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (1)) (Z_to_bv 64 (SHA (e_SBUF E + sbv + 4 + d))) (Z_to_bv 64 (5)) (Z_to_bv 64 (92)) (Z_to_bv 64 (e_SBUF E + sbv + 4 + d)) (Z_to_bv 64 (v)) xs11 xt3 xt4 xt5 xt6 F fc m1).
    Proof using OK SHZ KX HGS.
      intros p d v xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6 j64 j72 j80 j88 j96 j104 j112 j272 F fc m1 HR HP HM KH.
      pose proof (KH 1%Z ltac:(lia)) as KH1. pose proof (KH 2%Z ltac:(lia)) as KH2. pose proof (KH 3%Z ltac:(lia)) as KH3. pose proof (KH 4%Z ltac:(lia)) as KH4.
      s2_env OK.
      pose proof HM as HMo. s2_open_mem HMo.
      let fin := fun _ => (lazymatch goal with
                  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
                      lazymatch pc with
                      | 0xcb1dc%Z => eapply (KX 5%Z); [s2_errlit|]; s2_close_memx
                      | 0xbe0ec%Z =>
                          first [ replace (e_SBUF E + sbv + 4 + d + 1)%Z with (e_SBUF E + sbv + 4 + (d + 1))%Z by lia; eapply KH1; eassumption
                                | replace (e_SBUF E + sbv + 4 + d + 2)%Z with (e_SBUF E + sbv + 4 + (d + 2))%Z by lia; eapply KH2; eassumption
                                | replace (e_SBUF E + sbv + 4 + d + 3)%Z with (e_SBUF E + sbv + 4 + (d + 3))%Z by lia; eapply KH3; eassumption
                                | replace (e_SBUF E + sbv + 4 + d + 4)%Z with (e_SBUF E + sbv + 4 + (d + 4))%Z by lia; eapply KH4; eassumption ]
                      end
                  end) in
      let rec go _ := (repeat (lazymatch goal with
                               | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
                                   lazymatch pc with 0xbe0ec%Z => fail | 0xcb1dc%Z => fail | _ => idtac end
                               | _ => idtac end;
                               first [ gguard | wstep ]);
                       first [ fin tt | (let KB := fresh "KB" in if_cases KB; clear KB; go tt) ]) in
      go tt.
    Qed.

  End Loop.
End StrRm.
