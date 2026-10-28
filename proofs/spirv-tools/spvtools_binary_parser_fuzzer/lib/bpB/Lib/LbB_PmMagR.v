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

Lemma mg_shl_lo : forall x j, 0 <= x -> 0 <= j <= 64 ->
  Z_to_bv 64 (2 ^ (64 - j) * x) = Z_to_bv 64 (2 ^ (64 - j) * (x mod 2 ^ j)).
Proof.
  intros x j Hx Hj. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite (Z.div_mod x (2 ^ j)) at 1 by (apply Z.pow_nonzero; lia).
  replace (2 ^ (64 - j) * (2 ^ j * (x / 2 ^ j) + x mod 2 ^ j))
    with (2 ^ (64 - j) * (x mod 2 ^ j) + (x / 2 ^ j) * 2 ^ 64).
  - apply Z_mod_plus_full.
  - replace (2 ^ 64) with (2 ^ (64 - j) * 2 ^ j) by (rewrite <- Z.pow_add_r by lia; f_equal; lia). ring.
Qed.

Lemma mg_b1 : forall x, 0 <= x < 2 ^ 32 ->
  alu64 ALU_SRL (Z_to_bv 64 (281474976710656 * x)) (Z_to_bv 64 56) = Z_to_bv 64 ((x / 256) mod 256).
Proof.
  intros x Hx. change 281474976710656 with (2 ^ (64 - 16)). rewrite (mg_shl_lo x 16) by lia.
  change (2 ^ (64 - 16)) with 281474976710656. change (2 ^ 16) with 65536.
  pose proof (Z.mod_pos_bound x 65536 ltac:(lia)).
  rewrite w_srl by lia. f_equal. change (2 ^ 56) with 72057594037927936.
  Z.div_mod_to_equations. lia.
Qed.

Lemma mg_b2 : forall x, 0 <= x < 2 ^ 32 ->
  alu64 ALU_SRL (Z_to_bv 64 (1099511627776 * x)) (Z_to_bv 64 56) = Z_to_bv 64 ((x / 65536) mod 256).
Proof.
  intros x Hx. change 1099511627776 with (2 ^ (64 - 24)). rewrite (mg_shl_lo x 24) by lia.
  change (2 ^ (64 - 24)) with 1099511627776. change (2 ^ 24) with 16777216.
  pose proof (Z.mod_pos_bound x 16777216 ltac:(lia)).
  rewrite w_srl by lia. f_equal. change (2 ^ 56) with 72057594037927936.
  Z.div_mod_to_equations. lia.
Qed.

Lemma mg_land255 : forall a, Z.land a 255 = a mod 256.
Proof. intros a. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

Ltac mg_closeB := first [ sc_closeB | (cbn [sc_denot]; evs; wnormB; rewrite ?mg_b1, ?mg_b2, ?mg_land255 by lia; sc_brB) ].

Definition ha_E (R : bvmap 5 word) (q sp words n fp : Z) : env := Eseed R [Z_to_bv 64 0; Z_to_bv 64 q; Z_to_bv 64 sp; Z_to_bv 64 words; Z_to_bv 64 n; Z_to_bv 64 0; Z_to_bv 64 fp].
Definition ha_sr : list expr := srs sr_id [(2%bv, EVar 34); (9%bv, EVar 38); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (ELit 3456)); (19%bv, EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 33)) (ELit 2147450880)); (20%bv, EMd M_MUL (ELit 32) (EVar 33)); (22%bv, EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (ELit 3504))].
Definition ha_kn : list kentry := [KWord (SA (EMd M_MUL (ELit 32) (EVar 33)) 3504) 8 (EVar 35); KWord (SA (EMd M_MUL (ELit 32) (EVar 33)) 3512) 8 (EVar 36); KWord (SA (EVar 38) 40) 8 (ELit 2147450880); KWr (SA (EMd M_MUL (ELit 4) (EVar 33)) 2147451096) (ELit 2); KRange (EVar 34) (2 ^ 45 + 16) (2 ^ 47); KRange (EVar 38) (2 ^ 45) (2 ^ 47); KRange (EVar 33) 227200 (2 ^ 42); KRange (EVar 35) 16 (2 ^ 47); KRange (EVar 36) 5 (2 ^ 24)].
Definition ha_G_dirs : list bool := [].
Definition ha_G_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [965236] (SCR ha_G_dirs [] []) 963836 ha_sr ha_kn 60.
Definition ha_G_x := sym_exec bsegs 400 true [965236] (SCR ha_G_dirs [] []) (SS 963836 ha_sr [] ha_G_knF 60) [].
Definition ha_G_ss : sym_state := Eval vm_compute in fst (fst ha_G_x).
Definition ha_G_scs : list sidecond := Eval vm_compute in snd (fst ha_G_x).
Lemma ha_G_eq : ha_G_x = (ha_G_ss, ha_G_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma ha_G_pc : s_pc ha_G_ss = 965236.
Proof. reflexivity. Qed.
Lemma ha_G_sc : forall (R : bvmap 5 word) (m : word -> option byte) (q sp words n fp : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (2 ^ 45 <= fp <= 2 ^ 47) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) -> (16 <= words <= 2 ^ 47) -> (5 <= n <= 2 ^ 24) ->
  scs_denot bsegs m (ha_E R q sp words n fp) ha_G_scs.
Proof.
  intros R m q sp words n fp H0 H1 H2 H3 H4 H5 H6 H7. unfold ha_E, ha_G_scs. split_scs.
Qed.
Lemma ha_G_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (q sp words n fp : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (2 ^ 45 <= fp <= 2 ^ 47) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) -> (16 <= words <= 2 ^ 47) -> (5 <= n <= 2 ^ 24) ->
  regs_ok (ha_E R q sp words n fp) ha_sr R -> know_ok bsegs (ha_E R q sp words n fp) m ha_G_knF ->
  exists R', regs_ok (ha_E R q sp words n fp) (s_regs ha_G_ss) R' /\ log_flat (ha_E R q sp words n fp) (s_log ha_G_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 963836) m rom)
                    (mkst R' (Z_to_bv 64 965236) (mem_denot (ha_E R q sp words n fp) m (s_log ha_G_ss)) rom).
Proof.
  intros fx R m rom q sp words n fp H0 H1 H2 H3 H4 H5 H6 H7 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R ha_G_eq HR HK
              (ha_G_sc R m q sp words n fp H0 H1 H2 H3 H4 H5 H6 H7)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition mg_E (R : bvmap 5 word) (q sp words n x : Z) : env := Eseed R [Z_to_bv 64 0; Z_to_bv 64 q; Z_to_bv 64 sp; Z_to_bv 64 words; Z_to_bv 64 n; Z_to_bv 64 x].
Definition mg_sr : list expr := srs sr_id [(2%bv, EVar 34); (10%bv, EVar 35); (11%bv, EVar 36); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (ELit 3456)); (19%bv, EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 33)) (ELit 2147450880)); (20%bv, EMd M_MUL (ELit 32) (EVar 33)); (25%bv, EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (ELit 1728))].
Definition mg_kn : list kentry := [KWord (SA (ELit 0) 1593504) 8 (ELit 1642552); KWord (SA (ELit 0) 1642552) 8 (ELit 2147450880); KWord (SA (EVar 35) 0) 4 (EVar 37); KWr (SA (EMd M_MUL (ELit 32) (EVar 33)) 1728) (ELit 16); KWr (SA (EMd M_MUL (ELit 32) (EVar 33)) 3544) (ELit 4); KWr (SA (EMd M_MUL (ELit 32) (EVar 33)) 3548) (ELit 1); KWord (SA (EMd M_MUL (ELit 4) (EVar 33)) 2147451096) 1 (ELit 0); KWord (SA (EMd M_MUL (ELit 4) (EVar 33)) 2147451097) 1 (ELit 0); KWord (SA (EMd M_MUL (ELit 4) (EVar 33)) 2147451323) 1 (ELit 0); KWr (SA (EVar 34) (-16)) (ELit 16); KRange (EVar 34) (2 ^ 45 + 16) (2 ^ 47); KAlign (EVar 34) 16; KRange (EVar 33) 227200 (2 ^ 42); KRange (EVar 35) 16 (2 ^ 47); KAlign (EVar 35) 16; KRange (EVar 36) 5 (2 ^ 24); KRange (EVar 37) 0 (2 ^ 32 - 1); KDisj (SA (EVar 35) 0) (ELit 4) (SA (EMd M_MUL (ELit 32) (EVar 33)) 1728) (ELit 16); KDisj (SA (EVar 35) 0) (ELit 4) (SA (EVar 34) (-16)) (ELit 16); KDisj (SA (EMd M_MUL (ELit 32) (EVar 33)) 1728) (ELit 16) (SA (EVar 34) (-16)) (ELit 16); KDisj (SA (EVar 34) (-16)) (ELit 16) (SA (EMd M_MUL (ELit 32) (EVar 33)) 0) (ELit 4096); KDisj (SA (EVar 35) 0) (ELit 4) (SA (EMd M_MUL (ELit 32) (EVar 33)) 0) (ELit 4096)].
Definition mg_L_dirs : list bool := [false; false; false; false; false].
Definition mg_L_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [966084] (SCR mg_L_dirs [] []) 965236 mg_sr mg_kn 60.
Definition mg_L_x := sym_exec bsegs 400 true [966084] (SCR mg_L_dirs [] []) (SS 965236 mg_sr [] mg_L_knF 60) [].
Definition mg_L_ss : sym_state := Eval vm_compute in fst (fst mg_L_x).
Definition mg_L_scs : list sidecond := Eval vm_compute in snd (fst mg_L_x).
Lemma mg_L_eq : mg_L_x = (mg_L_ss, mg_L_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma mg_L_pc : s_pc mg_L_ss = 966084.
Proof. reflexivity. Qed.
Lemma mg_L_sc : forall (R : bvmap 5 word) (m : word -> option byte) (q sp words n x : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) -> (16 <= words <= 2 ^ 47) -> (words mod 16 = 0) -> (5 <= n <= 2 ^ 24) -> (0 <= x < 2 ^ 32) -> (x mod 256 = 3) -> ((x / 256) mod 256 = 2) -> ((x / 65536) mod 256 = 35) -> (x / 16777216 = 7) ->
  scs_denot bsegs m (mg_E R q sp words n x) mg_L_scs.
Proof.
  intros R m q sp words n x H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13. unfold mg_E, mg_L_scs. split_scs.
  - mg_closeB.
  - mg_closeB.
  - mg_closeB.
  - mg_closeB.
  - mg_closeB.
  - mg_closeB.
  - mg_closeB.
  - mg_closeB.
  - mg_closeB.
  - mg_closeB.
  - mg_closeB.
  - mg_closeB.
  - mg_closeB.
Qed.
Lemma mg_L_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (q sp words n x : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) -> (16 <= words <= 2 ^ 47) -> (words mod 16 = 0) -> (5 <= n <= 2 ^ 24) -> (0 <= x < 2 ^ 32) -> (x mod 256 = 3) -> ((x / 256) mod 256 = 2) -> ((x / 65536) mod 256 = 35) -> (x / 16777216 = 7) ->
  regs_ok (mg_E R q sp words n x) mg_sr R -> know_ok bsegs (mg_E R q sp words n x) m mg_L_knF ->
  exists R', regs_ok (mg_E R q sp words n x) (s_regs mg_L_ss) R' /\ log_flat (mg_E R q sp words n x) (s_log mg_L_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 965236) m rom)
                    (mkst R' (Z_to_bv 64 966084) (mem_denot (mg_E R q sp words n x) m (s_log mg_L_ss)) rom).
Proof.
  intros fx R m rom q sp words n x H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R mg_L_eq HR HK
              (mg_L_sc R m q sp words n x H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition mg_B_dirs : list bool := [true; false; false; false].
Definition mg_B_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [966084] (SCR mg_B_dirs [] []) 965236 mg_sr mg_kn 60.
Definition mg_B_x := sym_exec bsegs 400 true [966084] (SCR mg_B_dirs [] []) (SS 965236 mg_sr [] mg_B_knF 60) [].
Definition mg_B_ss : sym_state := Eval vm_compute in fst (fst mg_B_x).
Definition mg_B_scs : list sidecond := Eval vm_compute in snd (fst mg_B_x).
Lemma mg_B_eq : mg_B_x = (mg_B_ss, mg_B_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma mg_B_pc : s_pc mg_B_ss = 966084.
Proof. reflexivity. Qed.
Lemma mg_B_sc : forall (R : bvmap 5 word) (m : word -> option byte) (q sp words n x : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) -> (16 <= words <= 2 ^ 47) -> (words mod 16 = 0) -> (5 <= n <= 2 ^ 24) -> (0 <= x < 2 ^ 32) -> (x mod 256 = 7) -> ((x / 256) mod 256 = 35) -> ((x / 65536) mod 256 = 2) -> (x / 16777216 = 3) ->
  scs_denot bsegs m (mg_E R q sp words n x) mg_B_scs.
Proof.
  intros R m q sp words n x H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13. unfold mg_E, mg_B_scs. split_scs.
  - mg_closeB.
  - mg_closeB.
  - mg_closeB.
  - mg_closeB.
  - mg_closeB.
  - mg_closeB.
  - mg_closeB.
  - mg_closeB.
  - mg_closeB.
  - mg_closeB.
  - mg_closeB.
  - mg_closeB.
Qed.
Lemma mg_B_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (q sp words n x : Z),
  (2 ^ 45 + 16 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0x6e6000 + 0x9000 <= 32 * q) -> (32 * q + 4096 <= 2 ^ 47) -> ((32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)) -> (16 <= words <= 2 ^ 47) -> (words mod 16 = 0) -> (5 <= n <= 2 ^ 24) -> (0 <= x < 2 ^ 32) -> (x mod 256 = 7) -> ((x / 256) mod 256 = 35) -> ((x / 65536) mod 256 = 2) -> (x / 16777216 = 3) ->
  regs_ok (mg_E R q sp words n x) mg_sr R -> know_ok bsegs (mg_E R q sp words n x) m mg_B_knF ->
  exists R', regs_ok (mg_E R q sp words n x) (s_regs mg_B_ss) R' /\ log_flat (mg_E R q sp words n x) (s_log mg_B_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 965236) m rom)
                    (mkst R' (Z_to_bv 64 966084) (mem_denot (mg_E R q sp words n x) m (s_log mg_B_ss)) rom).
Proof.
  intros fx R m rom q sp words n x H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R mg_B_eq HR HK
              (mg_B_sc R m q sp words n x H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
