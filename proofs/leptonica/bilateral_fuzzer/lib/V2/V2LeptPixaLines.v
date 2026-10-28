(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV Reach.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac WalksLib W2Lib LeptDefs LeptStructs LeptArith LeptRoom LeptSlots LeptExec LeptExecW LeptExecFP LeptExecX DitherLib DitherLoop LeptCmapArr LeptExecB LeptArithB.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBase V2_code_pixaGetLinePtrs V2_code_pixaVerifyDepth.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require LeptRop.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.
(* [comment removed for export] *)
#[local] Opaque RiscvSemantics.store_ok.

Section Segs.
Variable rom : word -> option byte.
#[local] Existing Instance exf_fxd | 100.

Lemma pgd_run : forall (fx : FPState) regs (m : word -> option byte) (s pa parr i pix pd w h d : Z) (ret : word),
  (4096 + 128 <= s <= 2 ^ 47)%Z ->
  (s mod 8 = 0)%Z ->
  (4096 <= pa)%Z ->
  (pa + 32 <= 2 ^ 47)%Z ->
  (pa mod 8 = 0)%Z ->
  (4096 <= parr)%Z ->
  (parr + 80 <= 2 ^ 47)%Z ->
  (parr mod 8 = 0)%Z ->
  (0 <= i < 10)%Z ->
  (4096 <= pix)%Z ->
  (pix + 64 <= 2 ^ 47)%Z ->
  (pix mod 16 = 0)%Z ->
  (s <= pd)%Z ->
  (pd + 4 <= 2 ^ 47)%Z ->
  (pd mod 4 = 0)%Z ->
  (0 <= w < 2 ^ 31)%Z ->
  (0 <= h < 2 ^ 31)%Z ->
  (0 <= d < 2 ^ 31)%Z ->
  (pa + 32 <= s - 128 \/ pd + 4 <= pa)%Z ->
  (parr + 80 <= s - 128 \/ pd + 4 <= parr)%Z ->
  (pix + 64 <= s - 128 \/ pd + 4 <= pix)%Z ->
  (pix + 64 <= pa \/ pa + 32 <= pix)%Z ->
  (pix + 64 <= parr \/ parr + 80 <= pix)%Z ->
  rdn SEGS m (Z_to_bv 64 pa) 4 = Some (Z_to_le_bytes 4 10) ->
  rdn SEGS m (Z_to_bv 64 (pa + 16)) 8 = Some (Z_to_le_bytes 8 parr) ->
  rdn SEGS m (Z_to_bv 64 (parr + 8 * i)) 8 = Some (Z_to_le_bytes 8 pix) ->
  rdn SEGS m (Z_to_bv 64 pix) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (pix + 4)) 4 = Some (Z_to_le_bytes 4 h) ->
  rdn SEGS m (Z_to_bv 64 (pix + 8)) 4 = Some (Z_to_le_bytes 4 d) ->
  rdn SEGS m (Z_to_bv 64 (pix + 20)) 4 = Some (Z_to_le_bytes 4 1) ->
  (forall j, (0 <= j < 4)%Z -> m (Z_to_bv 64 (pix + 20 + j)) <> None) ->
  store_ok SEGS m (Z_to_bv 64 (s - 128)) 128 = true ->
  store_ok SEGS m (Z_to_bv 64 pd) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (pix + 20)) 4 = true ->
  getr regs 1 = ret ->
  ret_ok ret ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 pa ->
  getr regs 11 = Z_to_bv 64 i ->
  getr regs 12 = Z_to_bv 64 0 ->
  getr regs 13 = Z_to_bv 64 0 ->
  getr regs 14 = Z_to_bv 64 pd ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 100816) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' ret M' rom /\
      rinv [((s - 128)%Z, 128%Z); (pd, 4%Z)] m M' /\ rdn SEGS M' (Z_to_bv 64 pd) 4 = Some (Z_to_le_bytes 4 d) /\
      getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 s /\
      regs_agree (fun r => In r [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%list) regs regs').
Proof.
  intros fx regs m s pa parr i pix pd w h d ret Hs As Hpa1 Hpa2 Apa Hparr1 Hparr2 Aparr Hi Hpix1 Hpix2 Apix Hpd1 Hpd2 Apd Hw Hh Hd
    D1 D2 D3 D4 D5 R0 R16 Ri Rw Rh Rd Rrc Hnn SOK1 SOK2 SOK3 H1 Hret H2 H10 H11 H12 H13 H14.
  destruct fx as [fr cs].
  ex_entry regs [s; pa; parr; pix; pd; w; h; d] HR.
  assert (EM : edenot (ex_env regs [s; pa; parr; pix; pd; w; h; d]) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 11)) (EVar 34))
                = Z_to_bv 64 (8 * i + parr)).
  { change (edenot (ex_env regs [s; pa; parr; pix; pd; w; h; d]) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 11)) (EVar 34)))
      with (alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 8) (edenot (ex_env regs [s; pa; parr; pix; pd; w; h; d]) (EVar 11)))
              (edenot (ex_env regs [s; pa; parr; pix; pd; w; h; d]) (EVar 34))).
    replace (edenot (ex_env regs [s; pa; parr; pix; pd; w; h; d]) (EVar 11)) with (Z_to_bv 64 i) by (symmetry; ex_eden regs).
    replace (edenot (ex_env regs [s; pa; parr; pix; pd; w; h; d]) (EVar 34)) with (Z_to_bv 64 parr) by (symmetry; ex_eden regs).
    rewrite m_mul, zbv_mul. apply ex_ptr_val. }
  assert (HK : know_ok SEGS (ex_env regs [s; pa; parr; pix; pd; w; h; d]) m
    [KWr (SA (EVar 32) (-128)) 128; KWr (SA (EVar 36) 0) 4; KWr (SA (EVar 35) 20) 4;
     KRange (EVar 32) 4224 (2 ^ 47); KRange (EVar 33) 4096 (2 ^ 47 - 32); KRange (EVar 34) 4096 (2 ^ 47 - 80);
     KRange (EVar 35) 4096 (2 ^ 47 - 64); KAlign (EVar 35) 16; KRange (EVar 36) 4224 (2 ^ 47 - 4); KAlign (EVar 36) 4; KRange (EVar 11) 0 9;
     KAlign (EVar 32) 8; KAlign (EVar 33) 8; KAlign (EVar 34) 8;
     KRange (EVar 37) 0 (2 ^ 31 - 1); KRange (EVar 38) 0 (2 ^ 31 - 1); KRange (EVar 39) 0 (2 ^ 31 - 1);
     KWord (SA (EVar 33) 0) 4 (ELit 10); KWord (SA (EVar 33) 16) 8 (EVar 34);
     KAlign (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 11)) (EVar 34)) 8;
     KRange (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 11)) (EVar 34)) 4096 (2 ^ 47);
     KWord (SA (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 11)) (EVar 34)) 0) 8 (EVar 35);
     KWord (SA (EVar 35) 0) 4 (EVar 37); KWord (SA (EVar 35) 4) 4 (EVar 38); KWord (SA (EVar 35) 8) 4 (EVar 39);
     KWord (SA (EVar 35) 20) 4 (ELit 1);
     KDisj (SA (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 11)) (EVar 34)) 0) 8 (SA (EVar 32) (-128)) 128;
     KDisj (SA (EVar 33) 0) 32 (SA (EVar 32) (-128)) 128; KDisj (SA (EVar 34) 0) 80 (SA (EVar 32) (-128)) 128;
     KDisj (SA (EVar 35) 0) 64 (SA (EVar 32) (-128)) 128; KDisj (SA (EVar 36) 0) 4 (SA (EVar 32) (-128)) 128;
     KDisj (SA (EVar 35) 0) 64 (SA (EVar 33) 0) 32; KDisj (SA (EVar 35) 0) 64 (SA (EVar 34) 0) 80;
     KDisj (SA (EVar 35) 0) 64 (SA (EVar 36) 0) 4; KDisj (SA (EVar 33) 0) 32 (SA (EVar 36) 0) 4;
     KDisj (SA (EVar 34) 0) 80 (SA (EVar 36) 0) 4]).
  { ex_know regs.
    all: lazymatch goal with
         | |- kentry_ok _ _ _ (KAlign _ _) =>
             eapply ex_kalign; [exact EM | lia | lia | (replace (8 * i + parr)%Z with (parr + i * 8)%Z by ring; rewrite Z_mod_plus_full; exact Aparr)]
         | |- kentry_ok _ _ _ (KRange _ _ _) => eapply ex_krange; [exact EM | lia | lia]
         | |- kentry_ok _ _ _ (KWord _ _ _) =>
             eapply ex_kword_Z with (b := (8 * i + parr)%Z) (z := pix) (w := 8%nat);
             [exact EM | ex_eden regs | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia
             | (replace (8 * i + parr + 0)%Z with (parr + 8 * i)%Z by lia; exact Ri)]
         | |- kentry_ok _ _ _ (KDisj _ _ _ _) => eapply ex_kdisj; [exact EM | ex_eden regs | lia | lia | lia]
         end. }
  ex_open HR HK Hms Hlf.
  ex_cont 2000%nat (@nil Z) (SCR [false; false] [] []) HR Hlf HK Hms.
  all: try (lazymatch goal with |- reach _ _ _ => fail | _ => idtac end;
    rewrite ?m_mul, ?zbv_mul, ?ex_ptr_val;
    first [ (rewrite ?u_Z2bv by lia; lia) | ex_br
          | (rewrite ?alu_xor, ?alu_sltu; rewrite ?zbv_snez by lia; rewrite ?zbv_sltu_ge by lia; vm_compute; reflexivity) ]).
  pose proof I as FZ.
  lazymatch type of HR with regs_ok ?E ?sr ?R =>
  lazymatch type of Hms with msteps ?sg ?ms0 (@mkst (mkFP ?fr0 ?cs0) R (Z_to_bv 64 ?pc) (mem_denot E ?mm ?lg) ?rom0) =>
    assert (ST : ex_st sg E mm rom0 ms0 (mkFP (fr_denot E [] fr0) cs0) pc sr lg) by (exists R; exact (conj HR (conj Hlf Hms)))
  end end.
  clear HR Hlf Hms.
  exb_fstep (@nil (nat * nat)) HK ST FZ. exb_norm ST.
  exb_adriveS 8%nat 2000%nat [0%Z] (SCR [] [] []) (@nil (nat * nat)) HK ST FZ.
  exb_ret ST ret H1 Hret RR HR Hlf Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split.
  { apply (rinv_drop_cell SEGS _ m _ (pix + 20) 4%nat (Z_to_le_bytes 4 1)).
    - exB_rinv_tac Hlf [((s - 128)%Z, 128%Z); (pd, 4%Z); ((pix + 20)%Z, 4%Z)]; exB_reg_tac idtac.
    - lia.
    - change (Z.of_nat 4) with 4%Z; lia.
    - reflexivity.
    - change (Z.of_nat 4) with 4%Z; exact Hnn.
    - exact Rrc.
    - let C := fresh "C" in
      exB_cell HK Hlf (EVar 35) 20%Z 4%nat (pix + 20)%Z 1%Z C ltac:(exB_scs regs) ltac:(exB_tacA idtac) ltac:(exB_tacV idtac); exact C. }
  split; [let C := fresh "C" in
    exB_cell HK Hlf (EVar 36) 0%Z 4%nat pd d C ltac:(exB_scs regs) ltac:(exB_tacA idtac) ltac:(exB_tacV idtac); exact C|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR | ex_agree HRo HR ].
Qed.

Lemma pvd_head : forall (fx : FPState) regs (m : word -> option byte) (s pa ps : Z),
  (4096 + 256 <= s <= 2 ^ 47)%Z ->
  (4096 <= pa < 2 ^ 47)%Z ->
  (pa mod 8 = 0)%Z ->
  (s <= ps)%Z ->
  (ps + 4 <= 2 ^ 47)%Z ->
  (pa + 32 <= s - 64 \/ ps + 4 <= pa)%Z ->
  rdn SEGS m (Z_to_bv 64 pa) 4 = Some (Z_to_le_bytes 4 10) ->
  store_ok SEGS m (Z_to_bv 64 (s - 64)) 64 = true ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 pa ->
  getr regs 11 = Z_to_bv 64 ps ->
  getr regs 12 = Z_to_bv 64 0 ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 101144) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 100816) M' rom /\
      rinv [((s - 64)%Z, 64%Z)] m M' /\
      rdn SEGS M' (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 1)) /\ rdn SEGS M' (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)) /\ rdn SEGS M' (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 19)) /\ rdn SEGS M' (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 20)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 (getr regs 21)) /\
      getr regs' 1 = Z_to_bv 64 101252 /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 10 = Z_to_bv 64 pa /\ getr regs' 11 = Z_to_bv 64 0 /\
      getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 0 /\ getr regs' 14 = Z_to_bv 64 (s - 64) /\
      getr regs' 8 = Z_to_bv 64 pa /\ getr regs' 18 = Z_to_bv 64 0 /\ getr regs' 19 = Z_to_bv 64 ps /\ getr regs' 20 = Z_to_bv 64 10 /\
      regs_agree (fun r => In r [1; 2; 8; 18; 19; 20; 10; 11; 12; 13; 14]%list) regs regs').
Proof.
  intros fx regs m s pa ps Hs Hpa Apa Hps Hps4 Hdj Rpa SOK H2 H10 H11 H12.
  ex_entry regs [s; pa; ps] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pa; ps]) m
    [KWr (SA (EVar 32) (-64)) 64; KRange (EVar 32) (4096 + 256) (2 ^ 47); KRange (EVar 33) 4096 (2 ^ 47); KAlign (EVar 33) 8;
     KRange (EVar 34) 4096 (2 ^ 47); KWord (SA (EVar 33) 0) 4 (ELit 10); KDisj (SA (EVar 33) 0) 32 (SA (EVar 32) (-64)) 64]) by (ex_know regs).
  ex_open HR HK Hms Hlf.
  lazymatch goal with |- reach _ _ (fun _ => exists _ _, _ = @mkst _ _ (Z_to_bv 64 ?E) _ _ /\ _) =>
    ex_cont 400%nat [E] (SCR [] [] []) HR Hlf HK Hms end.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [exB_rinv_tac Hlf [((s - 64)%Z, 64%Z)]; exB_reg_tac idtac|].
  repeat match goal with |- _ /\ _ => split end.
  all: try (ex_reg regs HR); try (ex_agree HRo HR).
  all: lazymatch goal with |- rdn _ _ (Z_to_bv 64 (?s - ?k)) 8 = Some (word_to_le_bytes 8 ?x) =>
    let k' := eval cbv in (- k)%Z in let C := fresh "C" in
    exB_cellw HK Hlf (EVar 32) k' (s - k)%Z x C ltac:(exB_scs regs) ltac:(exB_tacA idtac) ltac:(exB_tacW); exact C end.
Qed.

Lemma pvd_first : forall (fx : FPState) regs (m : word -> option byte) (s pa ps : Z),
  (4096 + 256 <= s <= 2 ^ 47)%Z ->
  (4096 <= pa < 2 ^ 47)%Z ->
  (s <= ps)%Z ->
  (ps + 4 <= 2 ^ 47)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 64) ->
  getr regs 8 = Z_to_bv 64 pa ->
  getr regs 20 = Z_to_bv 64 10 ->
  getr regs 18 = Z_to_bv 64 0 ->
  getr regs 19 = Z_to_bv 64 ps ->
  getr regs 10 = Z_to_bv 64 0 ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 101252) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 100816) M' rom /\
      M' = m /\
      getr regs' 1 = Z_to_bv 64 101320 /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 10 = Z_to_bv 64 pa /\ getr regs' 12 = Z_to_bv 64 0 /\
      getr regs' 13 = Z_to_bv 64 0 /\ getr regs' 14 = Z_to_bv 64 (s - 60) /\ getr regs' 8 = Z_to_bv 64 pa /\ getr regs' 20 = Z_to_bv 64 10 /\
      getr regs' 21 = Z_to_bv 64 1 /\ getr regs' 18 = Z_to_bv 64 0 /\ getr regs' 19 = Z_to_bv 64 ps /\
      getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 9 = Z_to_bv 64 1 /\
      regs_agree (fun r => In r [1; 9; 10; 11; 12; 13; 14; 21]%list) regs regs').
Proof.
  intros fx regs m s pa ps Hs Hpa Hps Hps4 H2 H8 H20 H18 H19 H10.
  ex_entry regs [s; pa; ps] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pa; ps]) m
    [KRange (EVar 32) (4096 + 256) (2 ^ 47); KRange (EVar 33) 4096 (2 ^ 47); KRange (EVar 34) 4096 (2 ^ 47)]) by (ex_know regs).
  ex_open HR HK Hms Hlf.
  lazymatch goal with |- reach _ _ (fun _ => exists _ _, _ = @mkst _ _ (Z_to_bv 64 ?E) _ _ /\ _) =>
    ex_cont 400%nat [E] (SCR [] [] []) HR Hlf HK Hms end.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_agree HRo HR | exB_reg regs HR ].
Qed.

Lemma pvd_mid_more : forall (fx : FPState) regs (m : word -> option byte) (s pa ps i : Z),
  (4096 + 256 <= s <= 2 ^ 47)%Z ->
  (4096 <= pa < 2 ^ 47)%Z ->
  (s <= ps)%Z ->
  (ps + 4 <= 2 ^ 47)%Z ->
  (1 <= i <= 9)%Z ->
  (i + 1 < 10)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 64)) 4 = Some (Z_to_le_bytes 4 8) ->
  rdn SEGS m (Z_to_bv 64 (s - 60)) 4 = Some (Z_to_le_bytes 4 8) ->
  store_ok SEGS m (Z_to_bv 64 (s - 64)) 64 = true ->
  getr regs 2 = Z_to_bv 64 (s - 64) ->
  getr regs 8 = Z_to_bv 64 pa ->
  getr regs 20 = Z_to_bv 64 10 ->
  getr regs 18 = Z_to_bv 64 0 ->
  getr regs 19 = Z_to_bv 64 ps ->
  getr regs 10 = Z_to_bv 64 0 ->
  getr regs 9 = Z_to_bv 64 i ->
  getr regs 21 = Z_to_bv 64 1 ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 101320) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 100816) M' rom /\
      rinv [((s - 64)%Z, 4%Z)] m M' /\ rdn SEGS M' (Z_to_bv 64 (s - 64)) 4 = Some (Z_to_le_bytes 4 8) /\
      getr regs' 1 = Z_to_bv 64 101320 /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 10 = Z_to_bv 64 pa /\ getr regs' 12 = Z_to_bv 64 0 /\
      getr regs' 13 = Z_to_bv 64 0 /\ getr regs' 14 = Z_to_bv 64 (s - 60) /\ getr regs' 8 = Z_to_bv 64 pa /\ getr regs' 20 = Z_to_bv 64 10 /\
      getr regs' 21 = Z_to_bv 64 1 /\ getr regs' 18 = Z_to_bv 64 0 /\ getr regs' 19 = Z_to_bv 64 ps /\
      getr regs' 11 = Z_to_bv 64 (i + 1) /\ getr regs' 9 = Z_to_bv 64 (i + 1) /\
      regs_agree (fun r => In r [1; 9; 10; 11; 12; 13; 14; 21]%list) regs regs').
Proof.
  intros fx regs m s pa ps i Hs Hpa Hps Hps4 Hi Hi1 R64 R60 SOK H2 H8 H20 H18 H19 H10 H9 H21.
  ex_entry regs [s; pa; ps; i] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pa; ps; i]) m
    [KWr (SA (EVar 32) (-64)) 64; KRange (EVar 32) (4096 + 256) (2 ^ 47); KRange (EVar 33) 4096 (2 ^ 47); KRange (EVar 34) 4096 (2 ^ 47);
     KRange (EVar 35) 1 8; KWord (SA (EVar 32) (-64)) 4 (ELit 8); KWord (SA (EVar 32) (-60)) 4 (ELit 8)]) by (ex_know regs).
  ex_open HR HK Hms Hlf.
  lazymatch goal with |- reach _ _ (fun _ => exists _ _, _ = @mkst _ _ (Z_to_bv 64 ?E) _ _ /\ _) =>
    ex_cont 400%nat [E] (SCR [] [] []) HR Hlf HK Hms end.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [exB_rinv_tac Hlf [((s - 64)%Z, 4%Z)]; exB_reg_tac idtac|].
  split; [exB_cell HK Hlf (EVar 32) (-64)%Z 4%nat (s - 64)%Z 8%Z C ltac:(exB_scs regs) ltac:(exB_tacA idtac) ltac:(exB_tacV idtac); exact C|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_agree HRo HR | exB_reg regs HR ].
Qed.

Lemma pvd_mid_last : forall (fx : FPState) regs (m : word -> option byte) (s pa ps i : Z),
  (4096 + 256 <= s <= 2 ^ 47)%Z ->
  (4096 <= pa < 2 ^ 47)%Z ->
  (s <= ps)%Z ->
  (ps + 4 <= 2 ^ 47)%Z ->
  (1 <= i <= 9)%Z ->
  (i + 1 = 10)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 64)) 4 = Some (Z_to_le_bytes 4 8) ->
  rdn SEGS m (Z_to_bv 64 (s - 60)) 4 = Some (Z_to_le_bytes 4 8) ->
  store_ok SEGS m (Z_to_bv 64 (s - 64)) 64 = true ->
  getr regs 2 = Z_to_bv 64 (s - 64) ->
  getr regs 8 = Z_to_bv 64 pa ->
  getr regs 20 = Z_to_bv 64 10 ->
  getr regs 18 = Z_to_bv 64 0 ->
  getr regs 19 = Z_to_bv 64 ps ->
  getr regs 10 = Z_to_bv 64 0 ->
  getr regs 9 = Z_to_bv 64 i ->
  getr regs 21 = Z_to_bv 64 1 ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 101320) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 101428) M' rom /\
      rinv [((s - 64)%Z, 4%Z)] m M' /\ rdn SEGS M' (Z_to_bv 64 (s - 64)) 4 = Some (Z_to_le_bytes 4 8) /\
      getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 21 = Z_to_bv 64 1 /\ getr regs' 18 = Z_to_bv 64 0 /\ getr regs' 19 = Z_to_bv 64 ps /\
      regs_agree (fun r => In r [1; 9; 10; 11; 12; 13; 14; 21]%list) regs regs').
Proof.
  intros fx regs m s pa ps i Hs Hpa Hps Hps4 Hi Hi1 R64 R60 SOK H2 H8 H20 H18 H19 H10 H9 H21.
  assert ((i = 9)%Z) as -> by lia.
  ex_entry regs [s; pa; ps] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pa; ps]) m
    [KWr (SA (EVar 32) (-64)) 64; KRange (EVar 32) (4096 + 256) (2 ^ 47); KRange (EVar 33) 4096 (2 ^ 47); KRange (EVar 34) 4096 (2 ^ 47);
     KWord (SA (EVar 32) (-64)) 4 (ELit 8); KWord (SA (EVar 32) (-60)) 4 (ELit 8)]) by (ex_know regs).
  ex_open HR HK Hms Hlf.
  lazymatch goal with |- reach _ _ (fun _ => exists _ _, _ = @mkst _ _ (Z_to_bv 64 ?E) _ _ /\ _) =>
    ex_cont 400%nat [E] (SCR [] [] []) HR Hlf HK Hms end.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [exB_rinv_tac Hlf [((s - 64)%Z, 4%Z)]; exB_reg_tac idtac|].
  split; [exB_cell HK Hlf (EVar 32) (-64)%Z 4%nat (s - 64)%Z 8%Z C ltac:(exB_scs regs) ltac:(exB_tacA idtac) ltac:(exB_tacV idtac); exact C|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_agree HRo HR | exB_reg regs HR ].
Qed.

Lemma pvd_tail : forall (fx : FPState) regs (m : word -> option byte) (s ps : Z) (ret : word) (v1 v8 v9 v18 v19 v20 v21 : word),
  (4096 + 256 <= s <= 2 ^ 47)%Z ->
  (s <= ps)%Z ->
  (ps + 4 <= 2 ^ 47)%Z ->
  (ps mod 4 = 0)%Z ->
  ret_ok ret ->
  v1 = ret ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 v1) ->
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v8) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v9) ->
  rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v18) ->
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v19) ->
  rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 v20) ->
  rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 v21) ->
  store_ok SEGS m (Z_to_bv 64 ps) 4 = true ->
  getr regs 2 = Z_to_bv 64 (s - 64) ->
  getr regs 21 = Z_to_bv 64 1 ->
  getr regs 18 = Z_to_bv 64 0 ->
  getr regs 19 = Z_to_bv 64 ps ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 101428) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' ret M' rom /\
      rinv [(ps, 4%Z)] m M' /\ rdn SEGS M' (Z_to_bv 64 ps) 4 = Some (Z_to_le_bytes 4 1) /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 s /\
      getr regs' 8 = v8 /\ getr regs' 9 = v9 /\ getr regs' 18 = v18 /\ getr regs' 19 = v19 /\ getr regs' 20 = v20 /\ getr regs' 21 = v21 /\
      regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 10; 11]%list) regs regs').
Proof.
  intros fx regs m s ps ret v1 v8 v9 v18 v19 v20 v21 Hs Hps Hps4 Aps Hok E1 R1 R8 R9 R18 R19 R20 R21 SOKp H2 H21 H18 H19.
  subst v1.
  ex_entryL [ret; v8; v9; v18; v19; v20; v21] regs [s; ps] HR.
  assert (HK : know_ok SEGS (ex_envL [ret; v8; v9; v18; v19; v20; v21] regs [s; ps]) m
    [KWord (SA (EVar 39) (-8)) 8 (EVar 0); KWord (SA (EVar 39) (-16)) 8 (EVar 1); KWord (SA (EVar 39) (-24)) 8 (EVar 2);
     KWord (SA (EVar 39) (-32)) 8 (EVar 3); KWord (SA (EVar 39) (-40)) 8 (EVar 4); KWord (SA (EVar 39) (-48)) 8 (EVar 5);
     KWord (SA (EVar 39) (-56)) 8 (EVar 6);
     KWr (SA (EVar 40) 0) 4; KRange (EVar 40) 4096 (2 ^ 47); KAlign (EVar 40) 4; KRange (EVar 39) (4096 + 256) (2 ^ 47);
     KDisj (SA (EVar 40) 0) 4 (SA (EVar 39) (-64)) 64]) by (ex_know regs).
  ex_open HR HK Hms Hlf.
  ex_cont 400%nat [0%Z] (SCR [] [] []) HR Hlf HK Hms.
  lazymatch type of HR with regs_ok ?E ?sr ?R => lazymatch type of Hlf with log_flat _ ?lg =>
    lazymatch type of Hms with msteps ?sg ?ms0 (@mkst ?fxk _ (Z_to_bv 64 ?pc) (mem_denot _ ?bm _) ?rm) =>
      assert (ST : ex_st sg E bm rm ms0 fxk pc sr lg) by (exists R; split; [exact HR | split; [exact Hlf | exact Hms]]) end end end.
  exb_ret ST ret (eq_refl ret) Hok Rf HRf Hlff Hmsf.
  eexists; split; [exact Hmsf|].
  do 2 eexists; split; [reflexivity|].
  split; [exB_rinv_tac Hlff [(ps, 4%Z)]; exB_reg_tac idtac|].
  split; [exB_cell HK Hlff (EVar 40) 0%Z 4%nat ps 1%Z Hc ltac:(exB_scs regs) ltac:(exB_tacA idtac) ltac:(exB_tacV idtac); exact Hc|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_agree HRo HRf | exB_reg regs HRf ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pvd_mem (m : word -> option byte) (s pa parr w h : Z) (pixes : Z -> Z) : Prop :=
  (4096 <= pa)%Z /\ (pa + 32 <= s - 192)%Z /\ (pa mod 8 = 0)%Z /\ (4096 <= parr)%Z /\ (parr + 80 <= s - 192)%Z /\ (parr mod 8 = 0)%Z /\ (0 <= w < 2 ^ 31)%Z /\ (0 <= h < 2 ^ 31)%Z /\
  rdn SEGS m (Z_to_bv 64 pa) 4 = Some (Z_to_le_bytes 4 10) /\ rdn SEGS m (Z_to_bv 64 (pa + 16)) 8 = Some (Z_to_le_bytes 8 parr) /\
  forall i, (0 <= i < 10)%Z ->
    (4096 <= pixes i)%Z /\ (pixes i + 64 <= s - 192)%Z /\ (pixes i mod 16 = 0)%Z /\
    (pixes i + 64 <= pa \/ pa + 32 <= pixes i)%Z /\ (pixes i + 64 <= parr \/ parr + 80 <= pixes i)%Z /\
    rdn SEGS m (Z_to_bv 64 (parr + 8 * i)) 8 = Some (Z_to_le_bytes 8 (pixes i)) /\
    rdn SEGS m (Z_to_bv 64 (pixes i)) 4 = Some (Z_to_le_bytes 4 w) /\ rdn SEGS m (Z_to_bv 64 (pixes i + 4)) 4 = Some (Z_to_le_bytes 4 h) /\
    rdn SEGS m (Z_to_bv 64 (pixes i + 8)) 4 = Some (Z_to_le_bytes 4 8) /\ rdn SEGS m (Z_to_bv 64 (pixes i + 20)) 4 = Some (Z_to_le_bytes 4 1) /\
    (forall j, (0 <= j < 4)%Z -> m (Z_to_bv 64 (pixes i + 20 + j)) <> None) /\ store_ok SEGS m (Z_to_bv 64 (pixes i + 20)) 4 = true.

Lemma pvd_mem_keep : forall (m M : word -> option byte) (s pa parr w h : Z) (pixes : Z -> Z) (R : list (Z * Z)),
  pvd_mem m s pa parr w h pixes -> rinv R m M -> (s <= 2 ^ 47)%Z -> (forall r, In r R -> (s - 192 <= fst r)%Z) -> pvd_mem M s pa parr w h pixes.
Proof.
  intros m M s pa parr w h pixes R (Pa1 & Pa2 & Apa & Pr1 & Pr2 & Aparr & Hw & Hh & R0 & R16 & HP) RI Hs HR.
  pose proof (proj1 RI) as GR.
  assert (K : forall (z : Z) (n : nat), (0 <= z)%Z -> (z + Z.of_nat n <= s - 192)%Z ->
              rdn SEGS M (Z_to_bv 64 z) n = rdn SEGS m (Z_to_bv 64 z) n).
  { intros z n Hz Hzn. apply (rinv_rdn SEGS R m M z n RI Hz); [lia|].
    intros r Hr. specialize (HR r Hr). lia. }
  unfold pvd_mem. do 8 (split; [first [assumption | lia]|]).
  split; [rewrite K by lia; exact R0|].
  split; [rewrite K by lia; exact R16|].
  intros i Hi. destruct (HP i Hi) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12).
  do 5 (split; [assumption|]).
  split; [rewrite K by lia; exact X6|].
  split; [rewrite K by lia; exact X7|].
  split; [rewrite K by lia; exact X8|].
  split; [rewrite K by lia; exact X9|].
  split; [rewrite K by lia; exact X10|].
  split; [intros j Hj; exact (GR _ (X11 j Hj))|].
  exact (store_ok_mono SEGS 4 m M _ GR X12).
Qed.

(* [comment removed for export] *)
Definition RL (s : Z) : list (Z * Z) := [((s - 192)%Z, 128%Z); ((s - 64)%Z, 8%Z)].
Definition PVL : list reg := [1; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 21; 28; 29; 30; 31]%bv.

Lemma pvd_ag_keep : forall (L : list reg) regs regs' (r : reg) (v : word),
  regs_agree (fun x => In x L) regs regs' -> existsb (fun x => Z.eqb (bv_unsigned x) (bv_unsigned r)) L = false ->
  getr regs r = v -> getr regs' r = v.
Proof.
  intros L regs regs' r v AG E H. rewrite AG; [exact H|]. intros Hin.
  assert (T : existsb (fun x => Z.eqb (bv_unsigned x) (bv_unsigned r)) L = true).
  { apply existsb_exists. exists r. split; [exact Hin | apply Z.eqb_refl]. }
  congruence.
Qed.

Lemma pvd_ag_comp : forall (L1 L2 L : list reg) r1 r2 r3,
  regs_agree (fun x => In x L1) r1 r2 -> regs_agree (fun x => In x L2) r2 r3 ->
  forallb (fun x => existsb (fun y => Z.eqb (bv_unsigned y) (bv_unsigned x)) L) (L1 ++ L2) = true ->
  regs_agree (fun x => In x L) r1 r3.
Proof.
  intros L1 L2 L r1 r2 r3 A1 A2 B r Hr. rewrite forallb_forall in B.
  assert (IN : forall x, In x (L1 ++ L2) -> In x L).
  { intros x Hx. specialize (B x Hx). apply existsb_exists in B. destruct B as (y & Hy & E).
    apply Z.eqb_eq in E. apply bv_eq in E. subst. exact Hy. }
  rewrite A2, A1; [reflexivity | |].
  - intros Hin. apply Hr, IN, in_or_app. left. exact Hin.
  - intros Hin. apply Hr, IN, in_or_app. right. exact Hin.
Qed.

Lemma pvd_mod : forall s k q d : Z, (0 < q)%Z -> (0 < d)%Z -> (s mod d = 0)%Z -> (d mod q = 0)%Z -> (k mod q = 0)%Z -> ((s - k) mod q = 0)%Z.
Proof.
  intros s k q d Hq Hd Hs Hdq Hk.
  pose proof (proj1 (Z.mod_divide s d ltac:(lia)) Hs) as Ds.
  pose proof (proj1 (Z.mod_divide d q ltac:(lia)) Hdq) as Dd.
  pose proof (proj1 (Z.mod_divide k q ltac:(lia)) Hk) as Dk.
  apply (proj2 (Z.mod_divide (s - k) q ltac:(lia))).
  apply Z.divide_sub_r; [exact (Z.divide_trans _ _ _ Dd Ds) | exact Dk].
Qed.

Ltac pvd_agk AG H := apply (pvd_ag_keep _ _ _ _ _ AG); [vm_compute; reflexivity | exact H].
Ltac pvd_agc A1 A2 := eapply pvd_ag_comp; [exact A1 | exact A2 | vm_compute; reflexivity].
Ltac pvd_rd RI :=
  lazymatch goal with
  | |- rdn _ ?M (Z_to_bv 64 ?z) ?n = _ =>
      rewrite (rinv_rdn SEGS _ _ M z n RI) by (lazymatch goal with |- forall _ : _, _ => intros r Hr; cbn [In RL] in Hr; repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; lia|]); destruct Hr | _ => lia end)
  end.
Ltac pvd_sok GR SOK := eapply store_ok_mono; [exact GR|]; eapply store_ok_sub; [|exact SOK| |]; rewrite ?u_Z2bv by lia; lia.
Ltac pvd_in := cbn [In RL]; first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity].
Ltac pvd_pick L :=
  lazymatch L with
  | cons ?x ?tl => first [ exists x; split; [pvd_in | cbn [fst snd]; lia] | pvd_pick tl ]
  end.
Ltac pvd_wk H T :=
  let T' := eval cbv [RL] in T in
  eapply rinv_weaken; [exact H|];
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [In RL] in Hr;
  repeat (destruct Hr as [<-|Hr]; [pvd_pick T'|]); destruct Hr.
Ltac pvd_as := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
(* [comment removed for export] *)
Lemma pvd_loop : forall (n : nat) (fx : FPState) regs (M0 M : word -> option byte) (s pa parr ps w h i : Z) (pixes : Z -> Z),
  Z.of_nat n = (10 - i)%Z -> (1 <= i <= 9)%Z -> (4096 + 256 <= s <= 2 ^ 47)%Z -> (s mod 8 = 0)%Z -> (s <= ps)%Z -> (ps + 4 <= 2 ^ 47)%Z ->
  pvd_mem M0 s pa parr w h pixes -> store_ok SEGS M0 (Z_to_bv 64 (s - 192)) 192 = true -> rinv (RL s) M0 M ->
  rdn SEGS M (Z_to_bv 64 (s - 64)) 4 = Some (Z_to_le_bytes 4 8) ->
  getr regs 1 = Z_to_bv 64 101320 -> getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 10 = Z_to_bv 64 pa -> getr regs 11 = Z_to_bv 64 i ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 0 -> getr regs 14 = Z_to_bv 64 (s - 60) -> getr regs 8 = Z_to_bv 64 pa -> getr regs 9 = Z_to_bv 64 i ->
  getr regs 20 = Z_to_bv 64 10 -> getr regs 21 = Z_to_bv 64 1 -> getr regs 18 = Z_to_bv 64 0 -> getr regs 19 = Z_to_bv 64 ps ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 100816) M rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 101428) M' rom /\ rinv (RL s) M0 M' /\
                getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 21 = Z_to_bv 64 1 /\ getr regs' 18 = Z_to_bv 64 0 /\ getr regs' 19 = Z_to_bv 64 ps /\
                regs_agree (fun r => In r PVL) regs regs').
Proof.
  intros n. induction n as [|n IH];
    intros fx regs M0 M s pa parr ps w h i pixes Hn Hi Hs As Hps1 Hps2 PM0 SOK RI R64 H1 H2 H10 H11 H12 H13 H14 H8 H9 H20 H21 H18 H19.
  { lia. }
  assert (PM : pvd_mem M s pa parr w h pixes).
  { apply (pvd_mem_keep M0 M s pa parr w h pixes (RL s) PM0 RI ltac:(lia)).
    intros r Hr. cbn [In RL] in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; lia. }
  pose proof PM as (Pa1 & Pa2 & Apa & Pr1 & Pr2 & Aparr & Hw & Hh & Q0 & Q16 & HP).
  destruct (HP i ltac:(lia)) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12).
  pose proof (proj1 RI) as GR.
  eapply reach_bind.
  { apply (pgd_run fx regs M (s - 64)%Z pa parr i (pixes i) (s - 60)%Z w h 8%Z (getr regs 1)).
    all: first [ pvd_as | pvd_sok GR SOK | (rewrite H1; apply ret_ok_even; vm_compute; reflexivity)
               | (lazymatch goal with |- getr _ _ = getr _ _ => reflexivity end)
               | (apply (pvd_mod s _ _ 8); first [exact As | lia | reflexivity]) | lia ]. }
  intros fin1 (r1 & M1 & -> & RI1 & D1 & G10 & G2 & AG1).
  rewrite H1.
  assert (G8 : getr r1 8 = Z_to_bv 64 pa) by pvd_agk AG1 H8.
  assert (G9 : getr r1 9 = Z_to_bv 64 i) by pvd_agk AG1 H9.
  assert (G18 : getr r1 18 = Z_to_bv 64 0) by pvd_agk AG1 H18.
  assert (G19 : getr r1 19 = Z_to_bv 64 ps) by pvd_agk AG1 H19.
  assert (G20 : getr r1 20 = Z_to_bv 64 10) by pvd_agk AG1 H20.
  assert (G21 : getr r1 21 = Z_to_bv 64 1) by pvd_agk AG1 H21.
  assert (D64 : rdn SEGS M1 (Z_to_bv 64 (s - 64)) 4 = Some (Z_to_le_bytes 4 8)) by (pvd_rd RI1; exact R64).
  assert (GR1 : mem_grows M0 M1) by (eapply mem_grows_trans; [exact GR | exact (proj1 RI1)]).
  assert (SOK1 : store_ok SEGS M1 (Z_to_bv 64 (s - 64)) 64 = true) by pvd_sok GR1 SOK.
  assert (RIa : rinv (RL s) M0 M1) by (eapply rinv_trans; [exact RI | pvd_wk RI1 (RL s)]).
  destruct (Z.eq_dec (i + 1) 10) as [Hlast|Hmore].
  - eapply reach_weaken; [|apply (pvd_mid_last fx r1 M1 s pa ps i); first [pvd_as | lia]].
    intros fin (r2 & M2 & -> & RI2 & D2 & K2 & K21 & K18 & K19 & AG2).
    exists r2, M2. split; [reflexivity|].
    split; [eapply rinv_trans; [exact RIa | pvd_wk RI2 (RL s)]|].
    repeat match goal with |- _ /\ _ => split end; try pvd_as.
    pvd_agc AG1 AG2.
  - eapply reach_bind; [apply (pvd_mid_more fx r1 M1 s pa ps i); first [pvd_as | lia]|].
    intros fin2 (r2 & M2 & -> & RI2 & D2 & K1 & K2 & K10 & K12 & K13 & K14 & K8 & K20 & K21 & K18 & K19 & K11 & K9 & AG2).
    assert (RIb : rinv (RL s) M0 M2) by (eapply rinv_trans; [exact RIa | pvd_wk RI2 (RL s)]).
    assert (A12 : regs_agree (fun x => In x PVL) regs r2) by pvd_agc AG1 AG2.
    eapply reach_weaken; [|apply (IH fx r2 M0 M2 s pa parr ps w h (i + 1)%Z pixes); first [pvd_as | lia]].
    intros fin (r3 & M3 & -> & RI3 & L2 & L21 & L18 & L19 & AG3).
    exists r3, M3. split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; try pvd_as.
    pvd_agc A12 AG3.
Qed.

(* [comment removed for export] *)
Definition PVA : list reg := [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 28; 29; 30; 31]%bv.
Lemma pvd_run : forall (fx : FPState) regs (m : word -> option byte) (s pa parr ps w h : Z) (pixes : Z -> Z) (ret : word),
  (4096 + 256 <= s <= 2 ^ 47)%Z -> (s mod 8 = 0)%Z -> (s <= ps)%Z -> (ps + 4 <= 2 ^ 47)%Z -> (ps mod 4 = 0)%Z ->
  pvd_mem m s pa parr w h pixes -> store_ok SEGS m (Z_to_bv 64 (s - 192)) 192 = true -> store_ok SEGS m (Z_to_bv 64 ps) 4 = true ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 pa -> getr regs 11 = Z_to_bv 64 ps -> getr regs 12 = Z_to_bv 64 0 ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 101144) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' ret M' rom /\ rinv [((s - 192)%Z, 192%Z); (ps, 4%Z)] m M' /\
                rdn SEGS M' (Z_to_bv 64 ps) 4 = Some (Z_to_le_bytes 4 1) /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 s /\
                getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19 /\
                getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21 /\ regs_agree (fun r => In r PVA) regs regs').
Proof.
  intros fx regs m s pa parr ps w h pixes ret Hs As Hps1 Hps2 Aps PM SOK SOKp H1 Hret H2 H10 H11 H12.
  pose proof PM as (Pa1 & Pa2 & Apa & Pr1 & Pr2 & Aparr & Hw & Hh & R0 & R16 & HP).
  eapply reach_bind.
  { apply (pvd_head fx regs m s pa ps). all: first [ pvd_as | pvd_sok (mem_grows_refl m) SOK | lia ]. }
  intros fin1 (r1 & M1 & -> & RI1 & S8 & S16 & S24 & S32 & S40 & S48 & S56 & K1 & K2 & K10 & K11 & K12 & K13 & K14 & K8 & K18 & K19 & K20 & AG1).
  assert (PM1 : pvd_mem M1 s pa parr w h pixes).
  { apply (pvd_mem_keep m M1 s pa parr w h pixes _ PM RI1 ltac:(lia)).
    intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[]]. cbn [fst snd]. lia. }
  pose proof PM1 as (_ & _ & _ & _ & _ & _ & _ & _ & Q0 & Q16 & HQ).
  destruct (HQ 0%Z ltac:(lia)) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12).
  pose proof (proj1 RI1) as GR1.
  eapply reach_bind.
  { apply (pgd_run fx r1 M1 (s - 64)%Z pa parr 0%Z (pixes 0%Z) (s - 64)%Z w h 8%Z (getr r1 1)).
    all: first [ pvd_as | pvd_sok GR1 SOK | (rewrite K1; apply ret_ok_even; vm_compute; reflexivity)
               | (lazymatch goal with |- getr _ _ = getr _ _ => reflexivity end)
               | (apply (pvd_mod s _ _ 8); first [exact As | lia | reflexivity]) | lia ]. }
  intros fin2 (r2 & M2 & -> & RI2 & D2 & G10 & G2 & AG2).
  rewrite K1.
  assert (G8 : getr r2 8 = Z_to_bv 64 pa) by pvd_agk AG2 K8.
  assert (G18 : getr r2 18 = Z_to_bv 64 0) by pvd_agk AG2 K18.
  assert (G19 : getr r2 19 = Z_to_bv 64 ps) by pvd_agk AG2 K19.
  assert (G20 : getr r2 20 = Z_to_bv 64 10) by pvd_agk AG2 K20.
  eapply reach_bind; [apply (pvd_first fx r2 M2 s pa ps); first [pvd_as | lia]|].
  intros fin3 (r3 & M3 & -> & EM3 & L1 & L2 & L10 & L12 & L13 & L14 & L8 & L20 & L21 & L18 & L19 & L11 & L9 & AG3).
  subst M3.
  assert (RIa : rinv (RL s) M1 M2) by pvd_wk RI2 (RL s).
  assert (SOK1 : store_ok SEGS M1 (Z_to_bv 64 (s - 192)) 192 = true) by (eapply store_ok_mono; [exact GR1 | exact SOK]).
  eapply reach_bind; [apply (pvd_loop 9%nat fx r3 M1 M2 s pa parr ps w h 1%Z pixes); first [pvd_as | lia]|].
  intros fin4 (r4 & M4 & -> & RI4 & N2 & N21 & N18 & N19 & AG4).
  assert (GR4 : mem_grows m M4) by (eapply mem_grows_trans; [exact GR1 | exact (proj1 RI4)]).
  eapply reach_weaken; [|apply (pvd_tail fx r4 M4 s ps ret (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21));
    first [pvd_as | (pvd_rd RI4; pvd_as) | (eapply store_ok_mono; [exact GR4 | exact SOKp]) | lia]].
  intros fin (r5 & M5 & -> & RI5 & D5 & T10 & T2 & T8 & T9 & T18 & T19 & T20 & T21 & AG5).
  exists r5, M5. split; [reflexivity|].
  split.
  { eapply rinv_trans; [pvd_wk RI1 ([((s - 192)%Z, 192%Z)])|].
    eapply rinv_trans; [pvd_wk RI4 ([((s - 192)%Z, 192%Z)])|].
    pvd_wk RI5 ([(ps, 4%Z)]). }
  assert (A2 : regs_agree (fun x => In x PVA) regs r2) by pvd_agc AG1 AG2.
  assert (A3 : regs_agree (fun x => In x PVA) regs r3) by pvd_agc A2 AG3.
  assert (A4 : regs_agree (fun x => In x PVA) regs r4) by pvd_agc A3 AG4.
  repeat match goal with |- _ /\ _ => split end; try pvd_as.
  pvd_agc A4 AG5.
Qed.

Ltac post1 :=
  lazymatch goal with
  | |- regs_agree _ _ _ => solve_regs_agree
  | |- getr _ _ = _ => gres; pin; first [ reflexivity | apply bv_eq; rewrite ?u_Z2bv by lia; lia ]
  | |- _ = _ => first [ reflexivity | assumption ]
  end.
Ltac post := repeat (lazymatch goal with |- _ /\ _ => split end); post1.
Ltac cellw regs HK Hlf off a x :=
  let C := fresh "C" in
  exB_cellw HK Hlf (EVar 32) off a x C ltac:(exB_scs regs) ltac:(exB_tacA idtac) ltac:(exB_tacW); exact C.
Ltac cellz regs HK Hlf off n a z :=
  let C := fresh "C" in
  exB_cell HK Hlf (EVar 32) off n a z C ltac:(exB_scs regs) ltac:(exB_tacA idtac) ltac:(exB_tacV idtac); exact C.

Lemma gl_A : forall (fx : FPState) regs (m : word -> option byte) (s pa : Z),
  (4096 + 80 <= s <= 2 ^ 47)%Z ->
  (4096 <= pa)%Z ->
  (pa + 32 <= s - 80)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 80)) 80 = true ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 pa ->
  getr regs 11 = Z_to_bv 64 0 ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 101640) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 101144) M' rom /\
      rinv [((s - 80)%Z, 80%Z)] m M' /\
      rdn SEGS M' (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 1)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 19)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 20)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 (getr regs 21)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 (getr regs 22)) /\
      getr regs' 1 = Z_to_bv 64 101720 /\ getr regs' 2 = Z_to_bv 64 (s - 80) /\ getr regs' 10 = Z_to_bv 64 pa /\ getr regs' 11 = Z_to_bv 64 (s - 68) /\
      getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 8 = Z_to_bv 64 pa /\ getr regs' 9 = Z_to_bv 64 0 /\
      regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12]%list) regs regs').
Proof.
  intros fx regs m s pa Hs Hpa Hpas SOK H2 H10 H11.
  ex_entry regs [s; pa] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pa]) m
    [KWr (SA (EVar 32) (-80)) 80; KRange (EVar 33) 4096 (2 ^ 47)]) by (ex_know regs).
  ex_open HR HK Hms Hlf.
  ex_cont 200%nat [101144%Z] (SCR [] [] []) HR Hlf HK Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [exB_rinv_tac Hlf [((s - 80)%Z, 80%Z)]; exB_reg_tac idtac|].
  repeat match goal with |- _ /\ _ => split end.
  all: try (ex_reg regs HR); try (ex_agree HRo HR).
  all: lazymatch goal with |- rdn _ _ (Z_to_bv 64 (?s - ?k)) 8 = Some (word_to_le_bytes 8 ?x) =>
    let k' := eval cbv in (- k)%Z in cellw regs HK Hlf k' (s - k)%Z x end.
Qed.

Lemma gl_B : forall (fx : FPState) regs (m : word -> option byte) (s pa : Z),
  (4096 + 80 <= s <= 2 ^ 47)%Z ->
  (4096 <= pa)%Z ->
  (pa mod 8 = 0)%Z ->
  (pa + 32 <= s - 80)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 68)) 4 = Some (Z_to_le_bytes 4 1) ->
  rdn SEGS m (Z_to_bv 64 pa) 4 = Some (Z_to_le_bytes 4 10) ->
  getr regs 2 = Z_to_bv 64 (s - 80) ->
  getr regs 8 = Z_to_bv 64 pa ->
  getr regs 9 = Z_to_bv 64 0 ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 101720) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 246008) M' rom /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 101768 /\ getr regs' 10 = Z_to_bv 64 10 /\ getr regs' 11 = Z_to_bv 64 8 /\ getr regs' 19 = Z_to_bv 64 10 /\
      regs_agree (fun r => In r [1; 10; 11; 19]%list) regs regs').
Proof.
  intros fx regs m s pa Hs Hpa Apa Hpas R68 Rpa H2 H8 H9.
  ex_entry regs [s; pa] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pa]) m
    [KAlign (EVar 33) 8; KRange (EVar 33) 4096 (2 ^ 47); KWord (SA (EVar 32) (-68)) 4 (ELit 1); KWord (SA (EVar 33) 0) 4 (ELit 10)]) by (ex_know regs).
  ex_open HR HK Hms Hlf.
  ex_cont 400%nat [246008%Z] (SCR [] [] []) HR Hlf HK Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR | ex_agree HRo HR ].
Qed.

Lemma gl_C : forall (fx : FPState) regs (m : word -> option byte) (s ls : Z),
  (4096 + 80 <= s <= 2 ^ 47)%Z ->
  (4096 <= ls < 2 ^ 47)%Z ->
  (ls mod 8 = 0)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 80) ->
  getr regs 10 = Z_to_bv 64 ls ->
  getr regs 19 = Z_to_bv 64 10 ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 101768) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 101800) M' rom /\
      M' = m /\ getr regs' 9 = Z_to_bv 64 ls /\ getr regs' 18 = Z_to_bv 64 0 /\ getr regs' 19 = Z_to_bv 64 80 /\ getr regs' 20 = Z_to_bv 64 0 /\
      getr regs' 21 = Z_to_bv 64 (2 ^ 64 - 1 - ls) /\ getr regs' 22 = Z_to_bv 64 0 /\
      regs_agree (fun r => In r [9; 18; 19; 20; 21; 22]%list) regs regs').
Proof.
  intros fx regs m s ls Hs Hls Als H2 H10 H19.
  ex_entry regs [s; ls] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; ls]) m [KRange (EVar 33) 4096 (2 ^ 47); KAlign (EVar 33) 8]) by (ex_know regs).
  ex_open HR HK Hms Hlf.
  ex_cont 400%nat [101800%Z] (SCR [] [] []) HR Hlf HK Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end.
  all: try first [ ex_reg regs HR | ex_agree HRo HR ].
  all: change (v_xori (Z_to_bv 64 ls) (-1) = Z_to_bv 64 (2 ^ 64 - 1 - ls)); apply LeptRop.zbv_not; lia.
Qed.

Lemma gl_D : forall (fx : FPState) regs (m : word -> option byte) (s pa parr i pix : Z),
  (4096 + 144 <= s <= 2 ^ 47)%Z ->
  (4096 <= pa)%Z ->
  (pa mod 8 = 0)%Z ->
  (pa + 32 <= s - 144)%Z ->
  (4096 <= parr)%Z ->
  (parr mod 8 = 0)%Z ->
  (parr + 80 <= s - 144)%Z ->
  (0 <= i < 10)%Z ->
  (4096 <= pix)%Z ->
  (pix + 64 <= s - 144)%Z ->
  (pix mod 16 = 0)%Z ->
  (pix + 64 <= pa \/ pa + 32 <= pix)%Z ->
  (pix + 64 <= parr \/ parr + 80 <= pix)%Z ->
  rdn SEGS m (Z_to_bv 64 pa) 4 = Some (Z_to_le_bytes 4 10) ->
  rdn SEGS m (Z_to_bv 64 (pa + 16)) 8 = Some (Z_to_le_bytes 8 parr) ->
  rdn SEGS m (Z_to_bv 64 (parr + 8 * i)) 8 = Some (Z_to_le_bytes 8 pix) ->
  rdn SEGS m (Z_to_bv 64 (pix + 20)) 4 = Some (Z_to_le_bytes 4 1) ->
  store_ok SEGS m (Z_to_bv 64 (s - 144)) 144 = true ->
  store_ok SEGS m (Z_to_bv 64 (pix + 20)) 4 = true ->
  getr regs 2 = Z_to_bv 64 (s - 80) ->
  getr regs 8 = Z_to_bv 64 pa ->
  getr regs 18 = Z_to_bv 64 i ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 101800) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 109536) M' rom /\
      rinv [((s - 144)%Z, 72%Z); ((pix + 20)%Z, 4%Z)] m M' /\ rdn SEGS M' (Z_to_bv 64 (s - 80)) 8 = Some (Z_to_le_bytes 8 pix) /\
      rdn SEGS M' (Z_to_bv 64 (pix + 20)) 4 = Some (Z_to_le_bytes 4 2) /\
      getr regs' 1 = Z_to_bv 64 101828 /\ getr regs' 2 = Z_to_bv 64 (s - 80) /\ getr regs' 10 = Z_to_bv 64 pix /\ getr regs' 11 = Z_to_bv 64 0 /\
      regs_agree (fun r => In r [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%list) regs regs').
Proof.
  intros fx regs m s pa parr i pix Hs Hpa Apa Hpas Hparr Aparr Hparrs Hi Hpix Hpixs Apix Dpa Dparr Rn Rpp Rpi Rrc SOKf SOKp H2 H8 H18.
  destruct fx as [fr cs].
  ex_entry regs [s; pa; parr; i; pix] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pa; parr; i; pix]) m
    [KWr (SA (EVar 32) (-144)) 144; KWr (SA (EVar 36) 20) 4;
     KAlign (EVar 33) 8; KRange (EVar 33) 4096 (2 ^ 47); KAlign (EVar 34) 8; KRange (EVar 34) 4096 (2 ^ 47);
     KAlign (EVar 36) 16; KRange (EVar 36) 4096 (2 ^ 47); KRange (EVar 35) 0 9;
     KDisj (SA (EVar 32) (-144)) 144 (SA (EVar 33) 0) 32; KDisj (SA (EVar 32) (-144)) 144 (SA (EVar 34) 0) 80;
     KDisj (SA (EVar 32) (-144)) 144 (SA (EVar 36) 0) 64; KDisj (SA (EVar 36) 0) 64 (SA (EVar 33) 0) 32;
     KDisj (SA (EVar 36) 0) 64 (SA (EVar 34) 0) 80;
     KWord (SA (EVar 33) 0) 4 (ELit 10); KWord (SA (EVar 33) 16) 8 (EVar 34);
     KAlign (EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 8) (EVar 35))) 8;
     KRange (EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 8) (EVar 35))) 4096 (2 ^ 47);
     KWord (SA (EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 8) (EVar 35))) 0) 8 (EVar 36);
     KWord (SA (EVar 36) 20) 4 (ELit 1)]).
  { assert (EM : edenot (ex_env regs [s; pa; parr; i; pix]) (EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 8) (EVar 35))) = Z_to_bv 64 (parr + 8 * i)).
    { change (edenot (ex_env regs [s; pa; parr; i; pix]) (EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 8) (EVar 35))))
        with (alu64 ALU_ADD (edenot (ex_env regs [s; pa; parr; i; pix]) (EVar 34))
                (mul_div M_MUL (Z_to_bv 64 8) (edenot (ex_env regs [s; pa; parr; i; pix]) (EVar 35)))).
      replace (edenot (ex_env regs [s; pa; parr; i; pix]) (EVar 34)) with (Z_to_bv 64 parr) by (symmetry; ex_eden regs).
      replace (edenot (ex_env regs [s; pa; parr; i; pix]) (EVar 35)) with (Z_to_bv 64 i) by (symmetry; ex_eden regs).
      rewrite m_mul, zbv_mul. apply ex_ptr_val. }
    ex_know regs.
    1: eapply ex_kalign; [exact EM | lia | lia | (replace (parr + 8 * i)%Z with (parr + i * 8)%Z by ring; rewrite Z_mod_plus_full; exact Aparr)].
    1: eapply ex_krange; [exact EM | lia | lia].
    eapply (exx_kword_sum SEGS _ m (EVar 34) (EMd M_MUL (ELit 8) (EVar 35)) (EVar 36) parr (8 * i) 0 pix 8%nat).
    - ex_eden regs.
    - change (edenot (ex_env regs [s; pa; parr; i; pix]) (EMd M_MUL (ELit 8) (EVar 35)))
        with (mul_div M_MUL (Z_to_bv 64 8) (edenot (ex_env regs [s; pa; parr; i; pix]) (EVar 35))).
      replace (edenot (ex_env regs [s; pa; parr; i; pix]) (EVar 35)) with (Z_to_bv 64 i) by (symmetry; ex_eden regs).
      rewrite m_mul, zbv_mul. reflexivity.
    - ex_eden regs.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - rewrite Z.add_0_r. exact Rpi. }
  ex_open HR HK Hms Hlf.
  ex_cont 2000%nat [109536%Z] (SCR [false; false; false; false; false; false] [] []) HR Hlf HK Hms.
  all: try (lazymatch goal with |- reach _ _ _ => fail | _ => idtac end;
    rewrite ?m_mul, ?zbv_mul, ?ex_ptr_val;
    first [ (rewrite ?u_Z2bv by lia; lia) | ex_br
          | (rewrite ?alu_xor, ?alu_sltu; rewrite ?zbv_snez by lia; rewrite ?zbv_sltu_ge by lia; vm_compute; reflexivity) ]).
  pose proof I as FZ.
  lazymatch type of HR with regs_ok ?E ?sr ?R =>
  lazymatch type of Hms with msteps ?sg ?ms0 (@mkst (mkFP ?fr0 ?cs0) R (Z_to_bv 64 ?pc) (mem_denot E ?mm ?lg) ?rom0) =>
    assert (ST : ex_st sg E mm rom0 ms0 (mkFP (fr_denot E [] fr0) cs0) pc sr lg) by (exists R; exact (conj HR (conj Hlf Hms)))
  end end.
  clear HR Hlf Hms.
  exb_fstep (@nil (nat * nat)) HK ST FZ. exb_norm ST.
  exb_adriveS 8%nat 2000%nat [109536%Z] (SCR [] [] []) (@nil (nat * nat)) HK ST FZ.
  exb_exit ST RR HR Hlf Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [exB_rinv_tac Hlf [((s - 144)%Z, 72%Z); ((pix + 20)%Z, 4%Z)]; exB_reg_tac idtac|].
  split; [cellz regs HK Hlf (-80)%Z 8%nat (s - 80)%Z pix|].
  split; [let C := fresh "C" in
    exB_cell HK Hlf (EVar 36) 20%Z 4%nat (pix + 20)%Z 2%Z C ltac:(exB_scs regs) ltac:(exB_tacA idtac) ltac:(exB_tacV idtac); exact C|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR | ex_agree HRo HR ].
Qed.

Lemma gl_E_more : forall (fx : FPState) regs (m : word -> option byte) (s lsi pix lines i ls : Z),
  (4096 + 144 <= s <= 2 ^ 47)%Z ->
  (s mod 8 = 0)%Z ->
  (4096 <= lsi)%Z ->
  (lsi + 8 <= s - 144)%Z ->
  (4096 <= pix)%Z ->
  (pix + 64 <= s - 144)%Z ->
  (pix mod 16 = 0)%Z ->
  (0 <= lines < 2 ^ 47)%Z ->
  (0 <= i < 10)%Z ->
  (i + 1 < 10)%Z ->
  (0 <= ls < 2 ^ 47)%Z ->
  (lsi = ls + 8 * i)%Z ->
  (pix + 64 <= lsi \/ lsi + 8 <= pix)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some (Z_to_le_bytes 8 pix) ->
  rdn SEGS m (Z_to_bv 64 (pix + 20)) 4 = Some (Z_to_le_bytes 4 2) ->
  store_ok SEGS m (Z_to_bv 64 (s - 144)) 144 = true ->
  store_ok SEGS m (Z_to_bv 64 (pix + 20)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 lsi) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 80) ->
  getr regs 10 = Z_to_bv 64 lines ->
  getr regs 20 = Z_to_bv 64 (8 * i) ->
  getr regs 18 = Z_to_bv 64 i ->
  getr regs 9 = Z_to_bv 64 ls ->
  getr regs 19 = Z_to_bv 64 80 ->
  getr regs 21 = Z_to_bv 64 (2 ^ 64 - 1 - ls) ->
  getr regs 22 = Z_to_bv 64 0 ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 101828) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 101800) M' rom /\
      rinv [((s - 144)%Z, 72%Z); (lsi, 8%Z); ((pix + 20)%Z, 4%Z)] m M' /\ rdn SEGS M' (Z_to_bv 64 lsi) 8 = Some (Z_to_le_bytes 8 lines) /\
      rdn SEGS M' (Z_to_bv 64 (pix + 20)) 4 = Some (Z_to_le_bytes 4 1) /\ getr regs' 2 = Z_to_bv 64 (s - 80) /\
      getr regs' 18 = Z_to_bv 64 (i + 1) /\ getr regs' 20 = Z_to_bv 64 (8 * (i + 1)) /\
      regs_agree (fun r => In r [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 20; 28; 29; 30; 31]%list) regs regs').
Proof.
  intros fx regs m s lsi pix lines i ls.
  remember (2 ^ 64 - 1 - ls)%Z as nl eqn:Enl.
  intros Hs As Hlsi Hlsis Hpix Hpixs Apix Hlines Hi Hi1 Hls Elsi Dlp Rpix Rrc SOKf SOKp SOKl H2 H10 H20 H18 H9 H19 H21 H22.
  destruct fx as [fr cs].
  ex_entry regs [s; pix; lines; i; ls; (8 * i)%Z] HR.
  assert (EM : edenot (ex_env regs [s; pix; lines; i; ls; (8 * i)%Z]) (EAlu ALU_ADD (EVar 36) (EVar 37)) = Z_to_bv 64 lsi).
  { change (edenot (ex_env regs [s; pix; lines; i; ls; (8 * i)%Z]) (EAlu ALU_ADD (EVar 36) (EVar 37)))
      with (alu64 ALU_ADD (edenot (ex_env regs [s; pix; lines; i; ls; (8 * i)%Z]) (EVar 36))
              (edenot (ex_env regs [s; pix; lines; i; ls; (8 * i)%Z]) (EVar 37))).
    replace (edenot (ex_env regs [s; pix; lines; i; ls; (8 * i)%Z]) (EVar 36)) with (Z_to_bv 64 ls) by (symmetry; ex_eden regs).
    replace (edenot (ex_env regs [s; pix; lines; i; ls; (8 * i)%Z]) (EVar 37)) with (Z_to_bv 64 (8 * i)) by (symmetry; ex_eden regs).
    rewrite ex_ptr_val. f_equal. lia. }
  assert (HK : know_ok SEGS (ex_env regs [s; pix; lines; i; ls; (8 * i)%Z]) m
    [KWr (SA (EVar 32) (-144)) 144; KWr (SA (EVar 33) 20) 4; KWr (SA (EAlu ALU_ADD (EVar 36) (EVar 37)) 0) 8;
     KRange (EVar 32) 4240 (2 ^ 47); KAlign (EVar 32) 8; KAlign (EVar 33) 16; KRange (EVar 33) 4096 (2 ^ 47);
     KRange (EAlu ALU_ADD (EVar 36) (EVar 37)) 4096 (2 ^ 47); KRange (EVar 35) 0 8; KRange (EVar 37) 0 64;
     KWord (SA (EVar 32) (-80)) 8 (EVar 33); KWord (SA (EVar 33) 20) 4 (ELit 2)]).
  { ex_know regs.
    all: first [ (eapply ex_kwr; [exact EM | exact SOKl | lia | ex_natlia | lia | lia | lia | ex_natlia])
               | (eapply ex_krange; [exact EM | lia | lia]) ]. }
  ex_open HR HK Hms Hlf.
  ex_cont 2000%nat [101800%Z] (SCR [false; false; false] [] []) HR Hlf HK Hms.
  all: try (lazymatch goal with |- reach _ _ _ => fail | _ => idtac end;
    rewrite ?m_mul, ?zbv_mul, ?ex_ptr_val;
    first [ (rewrite ?u_Z2bv by lia; lia) | ex_br
          | (rewrite ?alu_xor, ?alu_sltu; rewrite ?zbv_snez by lia; rewrite ?zbv_sltu_ge by lia; vm_compute; reflexivity) ]).
  pose proof I as FZ.
  lazymatch type of HR with regs_ok ?E ?sr ?R =>
  lazymatch type of Hms with msteps ?sg ?ms0 (@mkst (mkFP ?fr0 ?cs0) R (Z_to_bv 64 ?pc) (mem_denot E ?mm ?lg) ?rom0) =>
    assert (ST : ex_st sg E mm rom0 ms0 (mkFP (fr_denot E [] fr0) cs0) pc sr lg) by (exists R; exact (conj HR (conj Hlf Hms)))
  end end.
  clear HR Hlf Hms.
  exb_fstep (@nil (nat * nat)) HK ST FZ. exb_norm ST.
  exb_adriveS 8%nat 2000%nat [101800%Z] (SCR [] [] []) (@nil (nat * nat)) HK ST FZ.
  exb_exit ST RR HR Hlf Hms.
  subst nl.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [exB_rinv_tac Hlf [((s - 144)%Z, 72%Z); (lsi, 8%Z); ((pix + 20)%Z, 4%Z)]; exB_reg_tac ltac:(rewrite ?ex_ptr_val)|].
  split; [let C := fresh "C" in
    exB_cell HK Hlf (EAlu ALU_ADD (EVar 36) (EVar 37)) 0%Z 8%nat lsi lines C ltac:(exB_scs regs)
      ltac:(exB_tacA ltac:(rewrite ?ex_ptr_val)) ltac:(exB_tacV idtac); exact C|].
  split; [let C := fresh "C" in
    exB_cell HK Hlf (EVar 33) 20%Z 4%nat (pix + 20)%Z 1%Z C ltac:(exB_scs regs) ltac:(exB_tacA idtac) ltac:(exB_tacV idtac); exact C|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR | ex_agree HRo HR ].
  all: apply LeptRop.addw_fit; lia.
Qed.

Lemma gl_E_last : forall (fx : FPState) regs (m : word -> option byte) (s lsi pix lines i ls : Z),
  (4096 + 144 <= s <= 2 ^ 47)%Z ->
  (s mod 8 = 0)%Z ->
  (4096 <= lsi)%Z ->
  (lsi + 8 <= s - 144)%Z ->
  (4096 <= pix)%Z ->
  (pix + 64 <= s - 144)%Z ->
  (pix mod 16 = 0)%Z ->
  (0 <= lines < 2 ^ 47)%Z ->
  (0 <= i < 10)%Z ->
  (i + 1 = 10)%Z ->
  (0 <= ls < 2 ^ 47)%Z ->
  (lsi = ls + 8 * i)%Z ->
  (pix + 64 <= lsi \/ lsi + 8 <= pix)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some (Z_to_le_bytes 8 pix) ->
  rdn SEGS m (Z_to_bv 64 (pix + 20)) 4 = Some (Z_to_le_bytes 4 2) ->
  store_ok SEGS m (Z_to_bv 64 (s - 144)) 144 = true ->
  store_ok SEGS m (Z_to_bv 64 (pix + 20)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 lsi) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 80) ->
  getr regs 10 = Z_to_bv 64 lines ->
  getr regs 20 = Z_to_bv 64 (8 * i) ->
  getr regs 18 = Z_to_bv 64 i ->
  getr regs 9 = Z_to_bv 64 ls ->
  getr regs 19 = Z_to_bv 64 80 ->
  getr regs 21 = Z_to_bv 64 (2 ^ 64 - 1 - ls) ->
  getr regs 22 = Z_to_bv 64 0 ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 101828) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 102048) M' rom /\
      rinv [((s - 144)%Z, 72%Z); (lsi, 8%Z); ((pix + 20)%Z, 4%Z)] m M' /\ rdn SEGS M' (Z_to_bv 64 lsi) 8 = Some (Z_to_le_bytes 8 lines) /\
      rdn SEGS M' (Z_to_bv 64 (pix + 20)) 4 = Some (Z_to_le_bytes 4 1) /\ getr regs' 2 = Z_to_bv 64 (s - 80) /\
      getr regs' 10 = Z_to_bv 64 ls /\
      regs_agree (fun r => In r [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 20; 28; 29; 30; 31]%list) regs regs').
Proof.
  intros fx regs m s lsi pix lines i ls.
  remember (2 ^ 64 - 1 - ls)%Z as nl eqn:Enl.
  intros Hs As Hlsi Hlsis Hpix Hpixs Apix Hlines Hi Hi1 Hls Elsi Dlp Rpix Rrc SOKf SOKp SOKl H2 H10 H20 H18 H9 H19 H21 H22.
  destruct fx as [fr cs].
  ex_entry regs [s; pix; lines; i; ls; (8 * i)%Z] HR.
  assert (EM : edenot (ex_env regs [s; pix; lines; i; ls; (8 * i)%Z]) (EAlu ALU_ADD (EVar 36) (EVar 37)) = Z_to_bv 64 lsi).
  { change (edenot (ex_env regs [s; pix; lines; i; ls; (8 * i)%Z]) (EAlu ALU_ADD (EVar 36) (EVar 37)))
      with (alu64 ALU_ADD (edenot (ex_env regs [s; pix; lines; i; ls; (8 * i)%Z]) (EVar 36))
              (edenot (ex_env regs [s; pix; lines; i; ls; (8 * i)%Z]) (EVar 37))).
    replace (edenot (ex_env regs [s; pix; lines; i; ls; (8 * i)%Z]) (EVar 36)) with (Z_to_bv 64 ls) by (symmetry; ex_eden regs).
    replace (edenot (ex_env regs [s; pix; lines; i; ls; (8 * i)%Z]) (EVar 37)) with (Z_to_bv 64 (8 * i)) by (symmetry; ex_eden regs).
    rewrite ex_ptr_val. f_equal. lia. }
  assert (HK : know_ok SEGS (ex_env regs [s; pix; lines; i; ls; (8 * i)%Z]) m
    [KWr (SA (EVar 32) (-144)) 144; KWr (SA (EVar 33) 20) 4; KWr (SA (EAlu ALU_ADD (EVar 36) (EVar 37)) 0) 8;
     KRange (EVar 32) 4240 (2 ^ 47); KAlign (EVar 32) 8; KAlign (EVar 33) 16; KRange (EVar 33) 4096 (2 ^ 47);
     KRange (EAlu ALU_ADD (EVar 36) (EVar 37)) 4096 (2 ^ 47); KRange (EVar 35) 9 9; KRange (EVar 37) 72 72;
     KWord (SA (EVar 32) (-80)) 8 (EVar 33); KWord (SA (EVar 33) 20) 4 (ELit 2)]).
  { ex_know regs.
    all: first [ (eapply ex_kwr; [exact EM | exact SOKl | lia | ex_natlia | lia | lia | lia | ex_natlia])
               | (eapply ex_krange; [exact EM | lia | lia]) ]. }
  ex_open HR HK Hms Hlf.
  ex_cont 2000%nat [102048%Z] (SCR [false; false; false] [] []) HR Hlf HK Hms.
  all: try (lazymatch goal with |- reach _ _ _ => fail | _ => idtac end;
    rewrite ?m_mul, ?zbv_mul, ?ex_ptr_val;
    first [ (rewrite ?u_Z2bv by lia; lia) | ex_br
          | (rewrite ?alu_xor, ?alu_sltu; rewrite ?zbv_snez by lia; rewrite ?zbv_sltu_ge by lia; vm_compute; reflexivity) ]).
  pose proof I as FZ.
  lazymatch type of HR with regs_ok ?E ?sr ?R =>
  lazymatch type of Hms with msteps ?sg ?ms0 (@mkst (mkFP ?fr0 ?cs0) R (Z_to_bv 64 ?pc) (mem_denot E ?mm ?lg) ?rom0) =>
    assert (ST : ex_st sg E mm rom0 ms0 (mkFP (fr_denot E [] fr0) cs0) pc sr lg) by (exists R; exact (conj HR (conj Hlf Hms)))
  end end.
  clear HR Hlf Hms.
  exb_fstep (@nil (nat * nat)) HK ST FZ. exb_norm ST.
  exb_adriveS 8%nat 2000%nat [102048%Z] (SCR [] [] []) (@nil (nat * nat)) HK ST FZ.
  exb_exit ST RR HR Hlf Hms.
  subst nl.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [exB_rinv_tac Hlf [((s - 144)%Z, 72%Z); (lsi, 8%Z); ((pix + 20)%Z, 4%Z)]; exB_reg_tac ltac:(rewrite ?ex_ptr_val)|].
  split; [let C := fresh "C" in
    exB_cell HK Hlf (EAlu ALU_ADD (EVar 36) (EVar 37)) 0%Z 8%nat lsi lines C ltac:(exB_scs regs)
      ltac:(exB_tacA ltac:(rewrite ?ex_ptr_val)) ltac:(exB_tacV idtac); exact C|].
  split; [let C := fresh "C" in
    exB_cell HK Hlf (EVar 33) 20%Z 4%nat (pix + 20)%Z 1%Z C ltac:(exB_scs regs) ltac:(exB_tacA idtac) ltac:(exB_tacV idtac); exact C|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR | ex_agree HRo HR ].
Qed.

Lemma gl_F : forall (fx : FPState) regs (m : word -> option byte) (s : Z) (ret : word) (v1 v8 v9 v18 v19 v20 v21 v22 : word),
  (4096 + 80 <= s <= 2 ^ 47)%Z ->
  ret_ok ret ->
  v1 = ret ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 v1) ->
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v8) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v9) ->
  rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v18) ->
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v19) ->
  rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 v20) ->
  rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 v21) ->
  rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 v22) ->
  getr regs 2 = Z_to_bv 64 (s - 80) ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 102048) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' ret M' rom /\
      M' = m /\ getr regs' 2 = Z_to_bv 64 s /\
      getr regs' 8 = v8 /\ getr regs' 9 = v9 /\ getr regs' 18 = v18 /\ getr regs' 19 = v19 /\ getr regs' 20 = v20 /\
      getr regs' 21 = v21 /\ getr regs' 22 = v22 /\
      regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 22]%list) regs regs').
Proof.
  intros fx regs m s ret v1 v8 v9 v18 v19 v20 v21 v22 Hs Hret E1 R1 R8 R9 R18 R19 R20 R21 R22 H2.
  subst v1. unfold reach. eexists. split.
  - norm_pc. stepLD8 F_18ea0 D_18ea0 ret.
    stepLD8 F_18ea4 D_18ea4 v8.
    stepLD8 F_18ea8 D_18ea8 v9.
    stepLD8 F_18eac D_18eac v18.
    stepLD8 F_18eb0 D_18eb0 v19.
    stepLD8 F_18eb4 D_18eb4 v20.
    stepLD8 F_18eb8 D_18eb8 v21.
    stepLD8 F_18ebc D_18ebc v22.
    zv F_18ec0 D_18ec0 (Z_to_bv 64 s).
    stepret F_18ec4 D_18ec4 ret ltac:(bveq).
    apply mst_refl.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.
End Segs.
