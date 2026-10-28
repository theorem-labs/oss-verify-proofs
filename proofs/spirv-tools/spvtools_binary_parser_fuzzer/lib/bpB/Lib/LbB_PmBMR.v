From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib HWord HUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_RwImg LbB_RwKit.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma bm_shl_lo : forall x j, 0 <= x -> 0 <= j <= 64 ->
  Z_to_bv 64 (2 ^ (64 - j) * x) = Z_to_bv 64 (2 ^ (64 - j) * (x mod 2 ^ j)).
Proof.
  intros x j Hx Hj. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite (Z.div_mod x (2 ^ j)) at 1 by (apply Z.pow_nonzero; lia).
  replace (2 ^ (64 - j) * (2 ^ j * (x / 2 ^ j) + x mod 2 ^ j))
    with (2 ^ (64 - j) * (x mod 2 ^ j) + (x / 2 ^ j) * 2 ^ 64).
  - apply Z_mod_plus_full.
  - replace (2 ^ 64) with (2 ^ (64 - j) * 2 ^ j) by (rewrite <- Z.pow_add_r by lia; f_equal; lia). ring.
Qed.

Lemma bm_b1 : forall x, 0 <= x < 2 ^ 32 ->
  alu64 ALU_SRL (Z_to_bv 64 (281474976710656 * x)) (Z_to_bv 64 56) = Z_to_bv 64 ((x / 256) mod 256).
Proof.
  intros x Hx. change 281474976710656 with (2 ^ (64 - 16)). rewrite (bm_shl_lo x 16) by lia.
  change (2 ^ (64 - 16)) with 281474976710656. change (2 ^ 16) with 65536.
  pose proof (Z.mod_pos_bound x 65536 ltac:(lia)).
  rewrite w_srl by lia. f_equal. change (2 ^ 56) with 72057594037927936.
  Z.div_mod_to_equations. lia.
Qed.

Lemma bm_b2 : forall x, 0 <= x < 2 ^ 32 ->
  alu64 ALU_SRL (Z_to_bv 64 (1099511627776 * x)) (Z_to_bv 64 56) = Z_to_bv 64 ((x / 65536) mod 256).
Proof.
  intros x Hx. change 1099511627776 with (2 ^ (64 - 24)). rewrite (bm_shl_lo x 24) by lia.
  change (2 ^ (64 - 24)) with 1099511627776. change (2 ^ 24) with 16777216.
  pose proof (Z.mod_pos_bound x 16777216 ltac:(lia)).
  rewrite w_srl by lia. f_equal. change (2 ^ 56) with 72057594037927936.
  Z.div_mod_to_equations. lia.
Qed.

Lemma bm_land255 : forall a, Z.land a 255 = a mod 256.
Proof. intros a. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

Ltac bm_closeB := first [ sc_closeB | (cbn [sc_denot]; evs; wnormB; rewrite ?bm_b1, ?bm_b2, ?bm_land255 by lia; sc_brB) ].

Definition bm_E (R : bvmap 5 word) (q sp words n x : Z) : env := Eseed R [Z_to_bv 64 0; Z_to_bv 64 q; Z_to_bv 64 sp; Z_to_bv 64 words; Z_to_bv 64 n; Z_to_bv 64 x].
Definition bm_sr : list expr := srs sr_id [(2%bv, EVar 34); (10%bv, EVar 35); (11%bv, EVar 36); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (ELit 3456)); (19%bv, EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 33)) (ELit 2147450880)); (20%bv, EMd M_MUL (ELit 32) (EVar 33)); (25%bv, EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (ELit 1728))].
Definition bm_kn : list kentry := [KWord (SA (ELit 0) 1593504) 8 (ELit 1642552); KWord (SA (ELit 0) 1642552) 8 (ELit 2147450880); KWord (SA (EVar 35) 0) 4 (EVar 37); KWr (SA (EMd M_MUL (ELit 32) (EVar 33)) 1728) (ELit 16); KWord (SA (EMd M_MUL (ELit 4) (EVar 33)) 2147451096) 1 (ELit 0); KWord (SA (EMd M_MUL (ELit 4) (EVar 33)) 2147451097) 1 (ELit 0); KWr (SA (EVar 34) (-16)) (ELit 16); KRange (EVar 33) 227200 (2 ^ 42); KRange (EVar 34) (2 ^ 45 + 16) (2 ^ 47); KAlign (EVar 34) 16; KRange (EVar 35) 16 (2 ^ 47); KAlign (EVar 35) 16; KRange (EVar 36) 5 (2 ^ 24); KRange (EVar 37) 0 (2 ^ 32 - 1); KDisj (SA (EVar 35) 0) (ELit 4) (SA (EMd M_MUL (ELit 32) (EVar 33)) 1728) (ELit 16); KDisj (SA (EVar 35) 0) (ELit 4) (SA (EVar 34) (-16)) (ELit 16); KDisj (SA (EMd M_MUL (ELit 32) (EVar 33)) 1728) (ELit 16) (SA (EVar 34) (-16)) (ELit 16); KDisj (SA (EVar 34) (-16)) (ELit 16) (SA (EMd M_MUL (ELit 32) (EVar 33)) 0) (ELit 4096); KDisj (SA (EVar 35) 0) (ELit 4) (SA (EMd M_MUL (ELit 32) (EVar 33)) 0) (ELit 4096)].
Definition bm_00_dirs : list bool := [false; true].
Definition bm_00_knF : list kentry := Eval vm_compute in kn_fixB 30 200 [965264] (SCR bm_00_dirs [] []) 965236 bm_sr bm_kn 60.
Definition bm_00_x := sym_exec bsegs 200 true [965264] (SCR bm_00_dirs [] []) (SS 965236 bm_sr [] bm_00_knF 60) [].
Definition bm_00_ss : sym_state := Eval vm_compute in fst (fst bm_00_x).
Definition bm_00_scs : list sidecond := Eval vm_compute in snd (fst bm_00_x).
Lemma bm_00_eq : bm_00_x = (bm_00_ss, bm_00_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma bm_00_pc : s_pc bm_00_ss = 965264.
Proof. reflexivity. Qed.
Lemma bm_00_sc : forall (R : bvmap 5 word) (m : word -> option byte) (q sp words n x : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) -> (16 <= words <= 2 ^ 47) -> (words mod 16 = 0) -> (5 <= n <= 2 ^ 24) -> (0 <= x < 2 ^ 32) -> (x mod 256 <> 3) -> (x mod 256 <> 7) ->
  scs_denot bsegs m (bm_E R q sp words n x) bm_00_scs.
Proof.
  intros R m q sp words n x H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11. unfold bm_E, bm_00_scs. split_scs.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
Qed.
Lemma bm_00_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (q sp words n x : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) -> (16 <= words <= 2 ^ 47) -> (words mod 16 = 0) -> (5 <= n <= 2 ^ 24) -> (0 <= x < 2 ^ 32) -> (x mod 256 <> 3) -> (x mod 256 <> 7) ->
  regs_ok (bm_E R q sp words n x) bm_sr R -> know_ok bsegs (bm_E R q sp words n x) m bm_00_knF ->
  exists R', regs_ok (bm_E R q sp words n x) (s_regs bm_00_ss) R' /\ log_flat (bm_E R q sp words n x) (s_log bm_00_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 965236) m rom)
                    (mkst R' (Z_to_bv 64 965264) (mem_denot (bm_E R q sp words n x) m (s_log bm_00_ss)) rom).
Proof.
  intros fx R m rom q sp words n x H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R bm_00_eq HR HK
              (bm_00_sc R m q sp words n x H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition bm_01_dirs : list bool := [true; true].
Definition bm_01_knF : list kentry := Eval vm_compute in kn_fixB 30 200 [965264] (SCR bm_01_dirs [] []) 965236 bm_sr bm_kn 60.
Definition bm_01_x := sym_exec bsegs 200 true [965264] (SCR bm_01_dirs [] []) (SS 965236 bm_sr [] bm_01_knF 60) [].
Definition bm_01_ss : sym_state := Eval vm_compute in fst (fst bm_01_x).
Definition bm_01_scs : list sidecond := Eval vm_compute in snd (fst bm_01_x).
Lemma bm_01_eq : bm_01_x = (bm_01_ss, bm_01_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma bm_01_pc : s_pc bm_01_ss = 965264.
Proof. reflexivity. Qed.
Lemma bm_01_sc : forall (R : bvmap 5 word) (m : word -> option byte) (q sp words n x : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) -> (16 <= words <= 2 ^ 47) -> (words mod 16 = 0) -> (5 <= n <= 2 ^ 24) -> (0 <= x < 2 ^ 32) -> (x mod 256 = 7) -> ((x / 256) mod 256 <> 35) ->
  scs_denot bsegs m (bm_E R q sp words n x) bm_01_scs.
Proof.
  intros R m q sp words n x H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11. unfold bm_E, bm_01_scs. split_scs.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
Qed.
Lemma bm_01_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (q sp words n x : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) -> (16 <= words <= 2 ^ 47) -> (words mod 16 = 0) -> (5 <= n <= 2 ^ 24) -> (0 <= x < 2 ^ 32) -> (x mod 256 = 7) -> ((x / 256) mod 256 <> 35) ->
  regs_ok (bm_E R q sp words n x) bm_sr R -> know_ok bsegs (bm_E R q sp words n x) m bm_01_knF ->
  exists R', regs_ok (bm_E R q sp words n x) (s_regs bm_01_ss) R' /\ log_flat (bm_E R q sp words n x) (s_log bm_01_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 965236) m rom)
                    (mkst R' (Z_to_bv 64 965264) (mem_denot (bm_E R q sp words n x) m (s_log bm_01_ss)) rom).
Proof.
  intros fx R m rom q sp words n x H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R bm_01_eq HR HK
              (bm_01_sc R m q sp words n x H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition bm_02_dirs : list bool := [true; false; true].
Definition bm_02_knF : list kentry := Eval vm_compute in kn_fixB 30 200 [965264] (SCR bm_02_dirs [] []) 965236 bm_sr bm_kn 60.
Definition bm_02_x := sym_exec bsegs 200 true [965264] (SCR bm_02_dirs [] []) (SS 965236 bm_sr [] bm_02_knF 60) [].
Definition bm_02_ss : sym_state := Eval vm_compute in fst (fst bm_02_x).
Definition bm_02_scs : list sidecond := Eval vm_compute in snd (fst bm_02_x).
Lemma bm_02_eq : bm_02_x = (bm_02_ss, bm_02_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma bm_02_pc : s_pc bm_02_ss = 965264.
Proof. reflexivity. Qed.
Lemma bm_02_sc : forall (R : bvmap 5 word) (m : word -> option byte) (q sp words n x : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) -> (16 <= words <= 2 ^ 47) -> (words mod 16 = 0) -> (5 <= n <= 2 ^ 24) -> (0 <= x < 2 ^ 32) -> (x mod 256 = 7) -> ((x / 256) mod 256 = 35) -> ((x / 65536) mod 256 <> 2) ->
  scs_denot bsegs m (bm_E R q sp words n x) bm_02_scs.
Proof.
  intros R m q sp words n x H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12. unfold bm_E, bm_02_scs. split_scs.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
Qed.
Lemma bm_02_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (q sp words n x : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) -> (16 <= words <= 2 ^ 47) -> (words mod 16 = 0) -> (5 <= n <= 2 ^ 24) -> (0 <= x < 2 ^ 32) -> (x mod 256 = 7) -> ((x / 256) mod 256 = 35) -> ((x / 65536) mod 256 <> 2) ->
  regs_ok (bm_E R q sp words n x) bm_sr R -> know_ok bsegs (bm_E R q sp words n x) m bm_02_knF ->
  exists R', regs_ok (bm_E R q sp words n x) (s_regs bm_02_ss) R' /\ log_flat (bm_E R q sp words n x) (s_log bm_02_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 965236) m rom)
                    (mkst R' (Z_to_bv 64 965264) (mem_denot (bm_E R q sp words n x) m (s_log bm_02_ss)) rom).
Proof.
  intros fx R m rom q sp words n x H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R bm_02_eq HR HK
              (bm_02_sc R m q sp words n x H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition bm_03_dirs : list bool := [true; false; false; true].
Definition bm_03_knF : list kentry := Eval vm_compute in kn_fixB 30 200 [965264] (SCR bm_03_dirs [] []) 965236 bm_sr bm_kn 60.
Definition bm_03_x := sym_exec bsegs 200 true [965264] (SCR bm_03_dirs [] []) (SS 965236 bm_sr [] bm_03_knF 60) [].
Definition bm_03_ss : sym_state := Eval vm_compute in fst (fst bm_03_x).
Definition bm_03_scs : list sidecond := Eval vm_compute in snd (fst bm_03_x).
Lemma bm_03_eq : bm_03_x = (bm_03_ss, bm_03_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma bm_03_pc : s_pc bm_03_ss = 965264.
Proof. reflexivity. Qed.
Lemma bm_03_sc : forall (R : bvmap 5 word) (m : word -> option byte) (q sp words n x : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) -> (16 <= words <= 2 ^ 47) -> (words mod 16 = 0) -> (5 <= n <= 2 ^ 24) -> (0 <= x < 2 ^ 32) -> (x mod 256 = 7) -> ((x / 256) mod 256 = 35) -> ((x / 65536) mod 256 = 2) -> (x / 16777216 <> 3) ->
  scs_denot bsegs m (bm_E R q sp words n x) bm_03_scs.
Proof.
  intros R m q sp words n x H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13. unfold bm_E, bm_03_scs. split_scs.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
Qed.
Lemma bm_03_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (q sp words n x : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) -> (16 <= words <= 2 ^ 47) -> (words mod 16 = 0) -> (5 <= n <= 2 ^ 24) -> (0 <= x < 2 ^ 32) -> (x mod 256 = 7) -> ((x / 256) mod 256 = 35) -> ((x / 65536) mod 256 = 2) -> (x / 16777216 <> 3) ->
  regs_ok (bm_E R q sp words n x) bm_sr R -> know_ok bsegs (bm_E R q sp words n x) m bm_03_knF ->
  exists R', regs_ok (bm_E R q sp words n x) (s_regs bm_03_ss) R' /\ log_flat (bm_E R q sp words n x) (s_log bm_03_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 965236) m rom)
                    (mkst R' (Z_to_bv 64 965264) (mem_denot (bm_E R q sp words n x) m (s_log bm_03_ss)) rom).
Proof.
  intros fx R m rom q sp words n x H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R bm_03_eq HR HK
              (bm_03_sc R m q sp words n x H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition bm_10_dirs : list bool := [false; false; true].
Definition bm_10_knF : list kentry := Eval vm_compute in kn_fixB 30 200 [965264] (SCR bm_10_dirs [] []) 965236 bm_sr bm_kn 60.
Definition bm_10_x := sym_exec bsegs 200 true [965264] (SCR bm_10_dirs [] []) (SS 965236 bm_sr [] bm_10_knF 60) [].
Definition bm_10_ss : sym_state := Eval vm_compute in fst (fst bm_10_x).
Definition bm_10_scs : list sidecond := Eval vm_compute in snd (fst bm_10_x).
Lemma bm_10_eq : bm_10_x = (bm_10_ss, bm_10_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma bm_10_pc : s_pc bm_10_ss = 965264.
Proof. reflexivity. Qed.
Lemma bm_10_sc : forall (R : bvmap 5 word) (m : word -> option byte) (q sp words n x : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) -> (16 <= words <= 2 ^ 47) -> (words mod 16 = 0) -> (5 <= n <= 2 ^ 24) -> (0 <= x < 2 ^ 32) -> (x mod 256 = 3) -> ((x / 256) mod 256 <> 2) ->
  scs_denot bsegs m (bm_E R q sp words n x) bm_10_scs.
Proof.
  intros R m q sp words n x H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11. unfold bm_E, bm_10_scs. split_scs.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
Qed.
Lemma bm_10_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (q sp words n x : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) -> (16 <= words <= 2 ^ 47) -> (words mod 16 = 0) -> (5 <= n <= 2 ^ 24) -> (0 <= x < 2 ^ 32) -> (x mod 256 = 3) -> ((x / 256) mod 256 <> 2) ->
  regs_ok (bm_E R q sp words n x) bm_sr R -> know_ok bsegs (bm_E R q sp words n x) m bm_10_knF ->
  exists R', regs_ok (bm_E R q sp words n x) (s_regs bm_10_ss) R' /\ log_flat (bm_E R q sp words n x) (s_log bm_10_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 965236) m rom)
                    (mkst R' (Z_to_bv 64 965264) (mem_denot (bm_E R q sp words n x) m (s_log bm_10_ss)) rom).
Proof.
  intros fx R m rom q sp words n x H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R bm_10_eq HR HK
              (bm_10_sc R m q sp words n x H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition bm_20_dirs : list bool := [false; false; false; true].
Definition bm_20_knF : list kentry := Eval vm_compute in kn_fixB 30 200 [965264] (SCR bm_20_dirs [] []) 965236 bm_sr bm_kn 60.
Definition bm_20_x := sym_exec bsegs 200 true [965264] (SCR bm_20_dirs [] []) (SS 965236 bm_sr [] bm_20_knF 60) [].
Definition bm_20_ss : sym_state := Eval vm_compute in fst (fst bm_20_x).
Definition bm_20_scs : list sidecond := Eval vm_compute in snd (fst bm_20_x).
Lemma bm_20_eq : bm_20_x = (bm_20_ss, bm_20_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma bm_20_pc : s_pc bm_20_ss = 965264.
Proof. reflexivity. Qed.
Lemma bm_20_sc : forall (R : bvmap 5 word) (m : word -> option byte) (q sp words n x : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) -> (16 <= words <= 2 ^ 47) -> (words mod 16 = 0) -> (5 <= n <= 2 ^ 24) -> (0 <= x < 2 ^ 32) -> (x mod 256 = 3) -> ((x / 256) mod 256 = 2) -> ((x / 65536) mod 256 <> 35) ->
  scs_denot bsegs m (bm_E R q sp words n x) bm_20_scs.
Proof.
  intros R m q sp words n x H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12. unfold bm_E, bm_20_scs. split_scs.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
Qed.
Lemma bm_20_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (q sp words n x : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) -> (16 <= words <= 2 ^ 47) -> (words mod 16 = 0) -> (5 <= n <= 2 ^ 24) -> (0 <= x < 2 ^ 32) -> (x mod 256 = 3) -> ((x / 256) mod 256 = 2) -> ((x / 65536) mod 256 <> 35) ->
  regs_ok (bm_E R q sp words n x) bm_sr R -> know_ok bsegs (bm_E R q sp words n x) m bm_20_knF ->
  exists R', regs_ok (bm_E R q sp words n x) (s_regs bm_20_ss) R' /\ log_flat (bm_E R q sp words n x) (s_log bm_20_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 965236) m rom)
                    (mkst R' (Z_to_bv 64 965264) (mem_denot (bm_E R q sp words n x) m (s_log bm_20_ss)) rom).
Proof.
  intros fx R m rom q sp words n x H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R bm_20_eq HR HK
              (bm_20_sc R m q sp words n x H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition bm_30_dirs : list bool := [false; false; false; false; true].
Definition bm_30_knF : list kentry := Eval vm_compute in kn_fixB 30 200 [965264] (SCR bm_30_dirs [] []) 965236 bm_sr bm_kn 60.
Definition bm_30_x := sym_exec bsegs 200 true [965264] (SCR bm_30_dirs [] []) (SS 965236 bm_sr [] bm_30_knF 60) [].
Definition bm_30_ss : sym_state := Eval vm_compute in fst (fst bm_30_x).
Definition bm_30_scs : list sidecond := Eval vm_compute in snd (fst bm_30_x).
Lemma bm_30_eq : bm_30_x = (bm_30_ss, bm_30_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma bm_30_pc : s_pc bm_30_ss = 965264.
Proof. reflexivity. Qed.
Lemma bm_30_sc : forall (R : bvmap 5 word) (m : word -> option byte) (q sp words n x : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) -> (16 <= words <= 2 ^ 47) -> (words mod 16 = 0) -> (5 <= n <= 2 ^ 24) -> (0 <= x < 2 ^ 32) -> (x mod 256 = 3) -> ((x / 256) mod 256 = 2) -> ((x / 65536) mod 256 = 35) -> (x / 16777216 <> 7) ->
  scs_denot bsegs m (bm_E R q sp words n x) bm_30_scs.
Proof.
  intros R m q sp words n x H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13. unfold bm_E, bm_30_scs. split_scs.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
  - bm_closeB.
Qed.
Lemma bm_30_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (q sp words n x : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) -> (16 <= words <= 2 ^ 47) -> (words mod 16 = 0) -> (5 <= n <= 2 ^ 24) -> (0 <= x < 2 ^ 32) -> (x mod 256 = 3) -> ((x / 256) mod 256 = 2) -> ((x / 65536) mod 256 = 35) -> (x / 16777216 <> 7) ->
  regs_ok (bm_E R q sp words n x) bm_sr R -> know_ok bsegs (bm_E R q sp words n x) m bm_30_knF ->
  exists R', regs_ok (bm_E R q sp words n x) (s_regs bm_30_ss) R' /\ log_flat (bm_E R q sp words n x) (s_log bm_30_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 965236) m rom)
                    (mkst R' (Z_to_bv 64 965264) (mem_denot (bm_E R q sp words n x) m (s_log bm_30_ss)) rom).
Proof.
  intros fx R m rom q sp words n x H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R bm_30_eq HR HK
              (bm_30_sc R m q sp words n x H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition bp_E (R : bvmap 5 word) (q sp : Z) : env := Eseed R [Z_to_bv 64 0; Z_to_bv 64 q; Z_to_bv 64 sp].
Definition bp_sr : list expr := srs sr_id [(2%bv, EVar 34); (19%bv, EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 33)) (ELit 2147450880)); (20%bv, EMd M_MUL (ELit 32) (EVar 33))].
Definition bp_kn : list kentry := [KWr (SA (EMd M_MUL (ELit 4) (EVar 33)) 2147450932) (ELit 218); KRange (EVar 33) 227200 (2 ^ 42); KRange (EVar 34) (2 ^ 45 + 16) (2 ^ 47); KAlign (EVar 34) 16].
Definition bp_A_dirs : list bool := [].
Definition bp_A_knF : list kentry := Eval vm_compute in kn_fixB 30 200 [756256] (SCR bp_A_dirs [] []) 965264 bp_sr bp_kn 60.
Definition bp_A_x := sym_exec bsegs 200 true [756256] (SCR bp_A_dirs [] []) (SS 965264 bp_sr [] bp_A_knF 60) [].
Definition bp_A_ss : sym_state := Eval vm_compute in fst (fst bp_A_x).
Definition bp_A_scs : list sidecond := Eval vm_compute in snd (fst bp_A_x).
Lemma bp_A_eq : bp_A_x = (bp_A_ss, bp_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma bp_A_pc : s_pc bp_A_ss = 756256.
Proof. reflexivity. Qed.
Lemma bp_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (q sp : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) ->
  scs_denot bsegs m (bp_E R q sp) bp_A_scs.
Proof.
  intros R m q sp H0 H1 H2 H3 H4 H5. unfold bp_E, bp_A_scs. split_scs.
Qed.
Lemma bp_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (q sp : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) ->
  regs_ok (bp_E R q sp) bp_sr R -> know_ok bsegs (bp_E R q sp) m bp_A_knF ->
  exists R', regs_ok (bp_E R q sp) (s_regs bp_A_ss) R' /\ log_flat (bp_E R q sp) (s_log bp_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 965264) m rom)
                    (mkst R' (Z_to_bv 64 756256) (mem_denot (bp_E R q sp) m (s_log bp_A_ss)) rom).
Proof.
  intros fx R m rom q sp H0 H1 H2 H3 H4 H5 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R bp_A_eq HR HK
              (bp_A_sc R m q sp H0 H1 H2 H3 H4 H5)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition tc_E (R : bvmap 5 word) (q sp ic pc : Z) : env := Eseed R [Z_to_bv 64 0; Z_to_bv 64 q; Z_to_bv 64 sp; Z_to_bv 64 ic; Z_to_bv 64 pc].
Definition tc_sr : list expr := srs sr_id [(2%bv, EVar 34); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (ELit 3456)); (19%bv, EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 33)) (ELit 2147450880)); (20%bv, EMd M_MUL (ELit 32) (EVar 33)); (24%bv, EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (ELit 416))].
Definition tc_kn : list kentry := [KWord (SA (EMd M_MUL (ELit 32) (EVar 33)) 3536) 8 (EVar 35); KWord (SA (EMd M_MUL (ELit 32) (EVar 33)) 3464) 8 (EVar 36); KWr (SA (EMd M_MUL (ELit 32) (EVar 33)) 432) (ELit 8); KWr (SA (EMd M_MUL (ELit 4) (EVar 33)) 2147450940) (ELit 3); KWr (SA (EMd M_MUL (ELit 32) (EVar 33)) 480) (ELit 2); KWr (SA (EMd M_MUL (ELit 32) (EVar 33)) 544) (ELit 2); KRange (EVar 33) 227200 (2 ^ 42); KRange (EVar 34) (2 ^ 45 + 16) (2 ^ 47); KAlign (EVar 34) 16; KRange (EVar 36) 16 (2 ^ 47); KAlign (EVar 36) 16].
Definition tc_A_dirs : list bool := [].
Definition tc_A_knF : list kentry := Eval vm_compute in kn_fixB 30 200 [1010964] (SCR tc_A_dirs [] []) 965508 tc_sr tc_kn 60.
Definition tc_A_x := sym_exec bsegs 200 true [1010964] (SCR tc_A_dirs [] []) (SS 965508 tc_sr [] tc_A_knF 60) [].
Definition tc_A_ss : sym_state := Eval vm_compute in fst (fst tc_A_x).
Definition tc_A_scs : list sidecond := Eval vm_compute in snd (fst tc_A_x).
Lemma tc_A_eq : tc_A_x = (tc_A_ss, tc_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma tc_A_pc : s_pc tc_A_ss = 1010964.
Proof. reflexivity. Qed.
Lemma tc_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (q sp ic pc : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) -> (16 <= pc <= 2 ^ 47) -> (pc mod 16 = 0) -> (0 <= ic < 2 ^ 64) ->
  scs_denot bsegs m (tc_E R q sp ic pc) tc_A_scs.
Proof.
  intros R m q sp ic pc H0 H1 H2 H3 H4 H5 H6 H7 H8. unfold tc_E, tc_A_scs. split_scs.
Qed.
Lemma tc_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (q sp ic pc : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) -> (16 <= pc <= 2 ^ 47) -> (pc mod 16 = 0) -> (0 <= ic < 2 ^ 64) ->
  regs_ok (tc_E R q sp ic pc) tc_sr R -> know_ok bsegs (tc_E R q sp ic pc) m tc_A_knF ->
  exists R', regs_ok (tc_E R q sp ic pc) (s_regs tc_A_ss) R' /\ log_flat (tc_E R q sp ic pc) (s_log tc_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 965508) m rom)
                    (mkst R' (Z_to_bv 64 1010964) (mem_denot (tc_E R q sp ic pc) m (s_log tc_A_ss)) rom).
Proof.
  intros fx R m rom q sp ic pc H0 H1 H2 H3 H4 H5 H6 H7 H8 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R tc_A_eq HR HK
              (tc_A_sc R m q sp ic pc H0 H1 H2 H3 H4 H5 H6 H7 H8)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition ts_E (R : bvmap 5 word) (q sp : Z) : env := Eseed R [Z_to_bv 64 0; Z_to_bv 64 q; Z_to_bv 64 sp].
Definition ts_sr : list expr := srs sr_id [(2%bv, EVar 34); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (ELit 1760)); (19%bv, EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 33)) (ELit 2147450880)); (20%bv, EMd M_MUL (ELit 32) (EVar 33)); (25%bv, EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (ELit 480)); (26%bv, EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (ELit 544))].
Definition ts_kn : list kentry := [KWord (SA (EMd M_MUL (ELit 32) (EVar 33)) 544) 1 (ELit 0); KWord (SA (EMd M_MUL (ELit 32) (EVar 33)) 480) 1 (ELit 0); KWr (SA (EMd M_MUL (ELit 4) (EVar 33)) 2147450932) (ELit 19); KRange (EVar 33) 227200 (2 ^ 42); KRange (EVar 34) (2 ^ 45 + 16) (2 ^ 47); KAlign (EVar 34) 16].
Definition ts_A_dirs : list bool := [].
Definition ts_A_knF : list kentry := Eval vm_compute in kn_fixB 30 200 [1008288] (SCR ts_A_dirs [] []) 965588 ts_sr ts_kn 60.
Definition ts_A_x := sym_exec bsegs 200 true [1008288] (SCR ts_A_dirs [] []) (SS 965588 ts_sr [] ts_A_knF 60) [].
Definition ts_A_ss : sym_state := Eval vm_compute in fst (fst ts_A_x).
Definition ts_A_scs : list sidecond := Eval vm_compute in snd (fst ts_A_x).
Lemma ts_A_eq : ts_A_x = (ts_A_ss, ts_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma ts_A_pc : s_pc ts_A_ss = 1008288.
Proof. reflexivity. Qed.
Lemma ts_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (q sp : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) ->
  scs_denot bsegs m (ts_E R q sp) ts_A_scs.
Proof.
  intros R m q sp H0 H1 H2 H3 H4 H5. unfold ts_E, ts_A_scs. split_scs.
Qed.
Lemma ts_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (q sp : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) ->
  regs_ok (ts_E R q sp) ts_sr R -> know_ok bsegs (ts_E R q sp) m ts_A_knF ->
  exists R', regs_ok (ts_E R q sp) (s_regs ts_A_ss) R' /\ log_flat (ts_E R q sp) (s_log ts_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 965588) m rom)
                    (mkst R' (Z_to_bv 64 1008288) (mem_denot (ts_E R q sp) m (s_log ts_A_ss)) rom).
Proof.
  intros fx R m rom q sp H0 H1 H2 H3 H4 H5 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R ts_A_eq HR HK
              (ts_A_sc R m q sp H0 H1 H2 H3 H4 H5)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition ha_E (R : bvmap 5 word) (q sp vt words x : Z) : env := Eseed R [Z_to_bv 64 0; Z_to_bv 64 q; Z_to_bv 64 sp; Z_to_bv 64 vt; Z_to_bv 64 words; Z_to_bv 64 x].
Definition ha_sr : list expr := srs sr_id [(2%bv, EVar 34); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (ELit 1760)); (19%bv, EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 33)) (ELit 2147450880)); (20%bv, EMd M_MUL (ELit 32) (EVar 33)); (22%bv, EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (ELit 3504)); (27%bv, ELit 2147450880)].
Definition ha_kn : list kentry := [KWord (SA (EMd M_MUL (ELit 32) (EVar 33)) 1760) 8 (EVar 35); KWord (SA (EVar 35) (-24)) 8 (ELit 112); KWord (SA (EMd M_MUL (ELit 32) (EVar 33)) 1880) 4 (ELit 4098); KWr (SA (EMd M_MUL (ELit 32) (EVar 33)) 1880) (ELit 4); KWord (SA (EMd M_MUL (ELit 32) (EVar 33)) 3504) 8 (EVar 36); KWord (SA (EVar 36) 0) 4 (EVar 37); KWord (SA (EMd M_MUL (ELit 4) (EVar 33)) 2147451115) 1 (ELit 0); KRange (EVar 33) 227200 (2 ^ 42); KRange (EVar 34) (2 ^ 45 + 16) (2 ^ 47); KAlign (EVar 34) 16; KRange (EVar 35) 24 (2 ^ 47 + 16); KRange (EVar 36) 16 (2 ^ 47); KAlign (EVar 36) 16; KRange (EVar 37) 0 (2 ^ 32 - 1); KDisj (SA (EVar 36) 0) (ELit 4) (SA (EMd M_MUL (ELit 32) (EVar 33)) 0) (ELit 4096)].
Definition ha_A_dirs : list bool := [].
Definition ha_A_knF : list kentry := Eval vm_compute in kn_fixB 30 200 [1200700] (SCR ha_A_dirs [] []) 965704 ha_sr ha_kn 60.
Definition ha_A_x := sym_exec bsegs 200 true [1200700] (SCR ha_A_dirs [] []) (SS 965704 ha_sr [] ha_A_knF 60) [].
Definition ha_A_ss : sym_state := Eval vm_compute in fst (fst ha_A_x).
Definition ha_A_scs : list sidecond := Eval vm_compute in snd (fst ha_A_x).
Lemma ha_A_eq : ha_A_x = (ha_A_ss, ha_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma ha_A_pc : s_pc ha_A_ss = 1200700.
Proof. reflexivity. Qed.
Lemma ha_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (q sp vt words x : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) -> (24 <= vt <= 2 ^ 47 + 16) -> (16 <= words <= 2 ^ 47) -> (words mod 16 = 0) -> (0 <= x < 2 ^ 32) ->
  scs_denot bsegs m (ha_E R q sp vt words x) ha_A_scs.
Proof.
  intros R m q sp vt words x H0 H1 H2 H3 H4 H5 H6 H7 H8 H9. unfold ha_E, ha_A_scs. split_scs.
  - bm_closeB.
Qed.
Lemma ha_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (q sp vt words x : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) -> (24 <= vt <= 2 ^ 47 + 16) -> (16 <= words <= 2 ^ 47) -> (words mod 16 = 0) -> (0 <= x < 2 ^ 32) ->
  regs_ok (ha_E R q sp vt words x) ha_sr R -> know_ok bsegs (ha_E R q sp vt words x) m ha_A_knF ->
  exists R', regs_ok (ha_E R q sp vt words x) (s_regs ha_A_ss) R' /\ log_flat (ha_E R q sp vt words x) (s_log ha_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 965704) m rom)
                    (mkst R' (Z_to_bv 64 1200700) (mem_denot (ha_E R q sp vt words x) m (s_log ha_A_ss)) rom).
Proof.
  intros fx R m rom q sp vt words x H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R ha_A_eq HR HK
              (ha_A_sc R m q sp vt words x H0 H1 H2 H3 H4 H5 H6 H7 H8 H9)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition hb_E (R : bvmap 5 word) (q sp vt words x : Z) : env := Eseed R [Z_to_bv 64 0; Z_to_bv 64 q; Z_to_bv 64 sp; Z_to_bv 64 vt; Z_to_bv 64 words; Z_to_bv 64 x].
Definition hb_sr : list expr := srs sr_id [(2%bv, EVar 34); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (ELit 1760)); (19%bv, EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 33)) (ELit 2147450880)); (20%bv, EMd M_MUL (ELit 32) (EVar 33)); (22%bv, EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (ELit 3504)); (27%bv, ELit 2147450880)].
Definition hb_kn : list kentry := [KWord (SA (EMd M_MUL (ELit 32) (EVar 33)) 1760) 8 (EVar 35); KWord (SA (EVar 35) (-24)) 8 (ELit 112); KWord (SA (EMd M_MUL (ELit 32) (EVar 33)) 1880) 4 (ELit 4104); KWr (SA (EMd M_MUL (ELit 32) (EVar 33)) 1880) (ELit 4); KWord (SA (EMd M_MUL (ELit 32) (EVar 33)) 3504) 8 (EVar 36); KWord (SA (EVar 36) 0) 4 (EVar 37); KWord (SA (EMd M_MUL (ELit 4) (EVar 33)) 2147451115) 1 (ELit 0); KRange (EVar 33) 227200 (2 ^ 42); KRange (EVar 34) (2 ^ 45 + 16) (2 ^ 47); KAlign (EVar 34) 16; KRange (EVar 35) 24 (2 ^ 47 + 16); KRange (EVar 36) 16 (2 ^ 47); KAlign (EVar 36) 16; KRange (EVar 37) 0 (2 ^ 32 - 1); KDisj (SA (EVar 36) 0) (ELit 4) (SA (EMd M_MUL (ELit 32) (EVar 33)) 0) (ELit 4096)].
Definition hb_A_dirs : list bool := [].
Definition hb_A_knF : list kentry := Eval vm_compute in kn_fixB 30 200 [1200700] (SCR hb_A_dirs [] []) 965704 hb_sr hb_kn 60.
Definition hb_A_x := sym_exec bsegs 200 true [1200700] (SCR hb_A_dirs [] []) (SS 965704 hb_sr [] hb_A_knF 60) [].
Definition hb_A_ss : sym_state := Eval vm_compute in fst (fst hb_A_x).
Definition hb_A_scs : list sidecond := Eval vm_compute in snd (fst hb_A_x).
Lemma hb_A_eq : hb_A_x = (hb_A_ss, hb_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma hb_A_pc : s_pc hb_A_ss = 1200700.
Proof. reflexivity. Qed.
Lemma hb_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (q sp vt words x : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) -> (24 <= vt <= 2 ^ 47 + 16) -> (16 <= words <= 2 ^ 47) -> (words mod 16 = 0) -> (0 <= x < 2 ^ 32) ->
  scs_denot bsegs m (hb_E R q sp vt words x) hb_A_scs.
Proof.
  intros R m q sp vt words x H0 H1 H2 H3 H4 H5 H6 H7 H8 H9. unfold hb_E, hb_A_scs. split_scs.
  - bm_closeB.
Qed.
Lemma hb_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (q sp vt words x : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) -> (24 <= vt <= 2 ^ 47 + 16) -> (16 <= words <= 2 ^ 47) -> (words mod 16 = 0) -> (0 <= x < 2 ^ 32) ->
  regs_ok (hb_E R q sp vt words x) hb_sr R -> know_ok bsegs (hb_E R q sp vt words x) m hb_A_knF ->
  exists R', regs_ok (hb_E R q sp vt words x) (s_regs hb_A_ss) R' /\ log_flat (hb_E R q sp vt words x) (s_log hb_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 965704) m rom)
                    (mkst R' (Z_to_bv 64 1200700) (mem_denot (hb_E R q sp vt words x) m (s_log hb_A_ss)) rom).
Proof.
  intros fx R m rom q sp vt words x H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R hb_A_eq HR HK
              (hb_A_sc R m q sp vt words x H0 H1 H2 H3 H4 H5 H6 H7 H8 H9)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition tq_E (R : bvmap 5 word) (q sp : Z) : env := Eseed R [Z_to_bv 64 0; Z_to_bv 64 q; Z_to_bv 64 sp].
Definition tq_sr : list expr := srs sr_id [(2%bv, EVar 34); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (ELit 1760)); (19%bv, EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 33)) (ELit 2147450880)); (20%bv, EMd M_MUL (ELit 32) (EVar 33))].
Definition tq_kn : list kentry := [KRange (EVar 33) 227200 (2 ^ 42); KRange (EVar 34) (2 ^ 45 + 16) (2 ^ 47); KAlign (EVar 34) 16].
Definition tq_A_dirs : list bool := [].
Definition tq_A_knF : list kentry := Eval vm_compute in kn_fixB 30 50 [1008288] (SCR tq_A_dirs [] []) 965824 tq_sr tq_kn 60.
Definition tq_A_x := sym_exec bsegs 50 true [1008288] (SCR tq_A_dirs [] []) (SS 965824 tq_sr [] tq_A_knF 60) [].
Definition tq_A_ss : sym_state := Eval vm_compute in fst (fst tq_A_x).
Definition tq_A_scs : list sidecond := Eval vm_compute in snd (fst tq_A_x).
Lemma tq_A_eq : tq_A_x = (tq_A_ss, tq_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma tq_A_pc : s_pc tq_A_ss = 1008288.
Proof. reflexivity. Qed.
Lemma tq_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (q sp : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) ->
  scs_denot bsegs m (tq_E R q sp) tq_A_scs.
Proof.
  intros R m q sp H0 H1 H2 H3 H4 H5. unfold tq_E, tq_A_scs. split_scs.
Qed.
Lemma tq_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (q sp : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) ->
  regs_ok (tq_E R q sp) tq_sr R -> know_ok bsegs (tq_E R q sp) m tq_A_knF ->
  exists R', regs_ok (tq_E R q sp) (s_regs tq_A_ss) R' /\ log_flat (tq_E R q sp) (s_log tq_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 965824) m rom)
                    (mkst R' (Z_to_bv 64 1008288) (mem_denot (tq_E R q sp) m (s_log tq_A_ss)) rom).
Proof.
  intros fx R m rom q sp H0 H1 H2 H3 H4 H5 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R tq_A_eq HR HK
              (tq_A_sc R m q sp H0 H1 H2 H3 H4 H5)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition td_E (R : bvmap 5 word) (q sp : Z) : env := Eseed R [Z_to_bv 64 0; Z_to_bv 64 q; Z_to_bv 64 sp].
Definition td_sr : list expr := srs sr_id [(2%bv, EVar 34); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (ELit 1760)); (19%bv, EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 33)) (ELit 2147450880)); (20%bv, EMd M_MUL (ELit 32) (EVar 33))].
Definition td_kn : list kentry := [KWord (SA (EMd M_MUL (ELit 32) (EVar 33)) 2120) 4 (ELit 4294967292); KRange (EVar 33) 227200 (2 ^ 42); KRange (EVar 34) (2 ^ 45 + 16) (2 ^ 47); KAlign (EVar 34) 16].
Definition td_A_dirs : list bool := [].
Definition td_A_knF : list kentry := Eval vm_compute in kn_fixB 30 50 [1034672] (SCR td_A_dirs [] []) 965844 td_sr td_kn 60.
Definition td_A_x := sym_exec bsegs 50 true [1034672] (SCR td_A_dirs [] []) (SS 965844 td_sr [] td_A_knF 60) [].
Definition td_A_ss : sym_state := Eval vm_compute in fst (fst td_A_x).
Definition td_A_scs : list sidecond := Eval vm_compute in snd (fst td_A_x).
Lemma td_A_eq : td_A_x = (td_A_ss, td_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma td_A_pc : s_pc td_A_ss = 1034672.
Proof. reflexivity. Qed.
Lemma td_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (q sp : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) ->
  scs_denot bsegs m (td_E R q sp) td_A_scs.
Proof.
  intros R m q sp H0 H1 H2 H3 H4 H5. unfold td_E, td_A_scs. split_scs.
Qed.
Lemma td_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (q sp : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) ->
  regs_ok (td_E R q sp) td_sr R -> know_ok bsegs (td_E R q sp) m td_A_knF ->
  exists R', regs_ok (td_E R q sp) (s_regs td_A_ss) R' /\ log_flat (td_E R q sp) (s_log td_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 965844) m rom)
                    (mkst R' (Z_to_bv 64 1034672) (mem_denot (td_E R q sp) m (s_log td_A_ss)) rom).
Proof.
  intros fx R m rom q sp H0 H1 H2 H3 H4 H5 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R td_A_eq HR HK
              (td_A_sc R m q sp H0 H1 H2 H3 H4 H5)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition te_E (R : bvmap 5 word) (q sp : Z) : env := Eseed R [Z_to_bv 64 0; Z_to_bv 64 q; Z_to_bv 64 sp].
Definition te_sr : list expr := srs sr_id [(2%bv, EVar 34); (19%bv, EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 33)) (ELit 2147450880)); (20%bv, EMd M_MUL (ELit 32) (EVar 33))].
Definition te_kn : list kentry := [KWr (SA (EMd M_MUL (ELit 4) (EVar 33)) 2147451100) (ELit 50); KRange (EVar 33) 227200 (2 ^ 42); KRange (EVar 34) (2 ^ 45 + 16) (2 ^ 47); KAlign (EVar 34) 16].
Definition te_A_dirs : list bool := [].
Definition te_A_knF : list kentry := Eval vm_compute in kn_fixB 30 100 [966900] (SCR te_A_dirs [] []) 965856 te_sr te_kn 60.
Definition te_A_x := sym_exec bsegs 100 true [966900] (SCR te_A_dirs [] []) (SS 965856 te_sr [] te_A_knF 60) [].
Definition te_A_ss : sym_state := Eval vm_compute in fst (fst te_A_x).
Definition te_A_scs : list sidecond := Eval vm_compute in snd (fst te_A_x).
Lemma te_A_eq : te_A_x = (te_A_ss, te_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma te_A_pc : s_pc te_A_ss = 966900.
Proof. reflexivity. Qed.
Lemma te_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (q sp : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) ->
  scs_denot bsegs m (te_E R q sp) te_A_scs.
Proof.
  intros R m q sp H0 H1 H2 H3 H4 H5. unfold te_E, te_A_scs. split_scs.
Qed.
Lemma te_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (q sp : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) ->
  regs_ok (te_E R q sp) te_sr R -> know_ok bsegs (te_E R q sp) m te_A_knF ->
  exists R', regs_ok (te_E R q sp) (s_regs te_A_ss) R' /\ log_flat (te_E R q sp) (s_log te_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 965856) m rom)
                    (mkst R' (Z_to_bv 64 966900) (mem_denot (te_E R q sp) m (s_log te_A_ss)) rom).
Proof.
  intros fx R m rom q sp H0 H1 H2 H3 H4 H5 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R te_A_eq HR HK
              (te_A_sc R m q sp H0 H1 H2 H3 H4 H5)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
