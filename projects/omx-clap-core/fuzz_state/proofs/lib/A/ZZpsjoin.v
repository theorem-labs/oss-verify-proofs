(* SCRATCH (a Theorem Labs lane): the four joins between put_string's call sites, image A (fs.asan), folded by
   a Theorem Labs lane into FSW_put_string.v. Every address and register map below is MEASURED by vm_compute over the pinned
   fs.asan through FSW_writer_tbl.fsw_wr_tbl (never read off a listing).
   Template (structure only, no proof term taken): the bespoke ASan line
   a Theorem Labs lane's put_string_blocksF.v
   - ps_after_open_first_F (:298-338): 0x85bec .. PS_HEAD writes seven words at [A + 8, A + 64);
   - ps_after_open_empty_F (:266-295): 0x85bec .. the put call, no write, a2 = 0;
   - ps_head_plain_end_F (:390-437): the register file at PS_END.
   MEASURED here (a build machine, workspace (internal path)):
   - from PS_OPEN_RET with only the string's first byte (read-only) and SH = [mkSHE 26 0 1], K = 60: the token run
     stops at 0x85bfc `TS_stopped (SR_load (Some 26%nat) 0)`, sh_j = 2, sh_obls = [], x10 / x11 := tokens 60 / 61;
     sh_static_ok needs the atom fact of 26 (without it: false, and the run stops at the shadow address of s);
   - from that cut, with the byte on atom 48 (fact [lo, hi] of psl_rng only) and the stack window [sp1 + 8, sp1 + 64):
     PSL_HEAD 0x85c58 `RS_running` in all three ranges; the seven words written are psj_scs7;
   - the byte 0 (fact [0, 0] and the condition `48 = 0`): A_put 0x8418c `RS_running`, no write, a0 = o, a1 = s, a2 = 0,
     ra = PS_END_RET 0x85d88;
   - from PSL_END with the two slots sp1 + 8 / sp1 + 16 (read-only, value esc - 32 = the frame): A_put `RS_running`,
     a0 = o, a1 = r, a2 = q - r (x24 - x26), ra = PS_END_RET, x21 := [sp1 + 16], x24 := [sp1 + 8];
   - from PS_END_RET with NO region and NO fact: A_put `RS_running`, a0 = o, a1 = PS_Q1, a2 = 1, ra = PS_CLOSE_RET. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YCeo.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_ret FSW_frame
FSW_frame3 FSW_writer_tbl FSW_writer_model FSW_put_string.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSH_Fn_writer FSW_writer_kit.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================= the closed shapes and the measured runs ================= *)
Definition PSJ_LOAD0 : Z := 0x85bfc.     (* the data load of s[0]: THE CUT of the opening stretch *)
(* the frame-pointer slot the state carries at the opening put's return *)
Definition psj_scs0 : list YP09.chunk := [YP09.mkChunk 80 (CVal 8 (SOff 24 0))].
(* the seven words the stretch PS_OPEN_RET .. PSL_HEAD writes at sp1 + 8 .. sp1 + 64 (MEASURED, in the run's order):
   the frame twice (+8, +16: the two words PSL_END reloads into x24 / x21) and five image addresses *)
Definition psj_scs7 : list YP09.chunk :=
  [YP09.mkChunk 56 (CVal 8 (SLit 135776)); YP09.mkChunk 24 (CVal 8 (SLit 135872));
   YP09.mkChunk 32 (CVal 8 (SLit 135904)); YP09.mkChunk 40 (CVal 8 (SLit 135808));
   YP09.mkChunk 48 (CVal 8 (SLit 135840)); YP09.mkChunk 8 (CVal 8 (SOff 24 0));
   YP09.mkChunk 16 (CVal 8 (SOff 24 0))].
(* the slots of the re-aligned frame (atom 9) after the opening stretch: scs1 *)
Definition psj_scs1 : list YP09.chunk := psj_scs7 ++ psj_scs0.

(* ---- the token run over s[0]'s inline shadow check ---- *)
Definition psj_SH : list shent := [mkSHE 26 0 1].
Definition psj_GT : facts :=
  mkFacts [(26%nat, mkAF 4096 (2 ^ 47 - 8) 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition psj_str0 : YP09.region := YP09.mkRegion (Some 26%nat) 0 1 0 0 [].
Definition psj_ssT : sstate := mkSS PS_OPEN_RET ps_ret_regs [psj_str0] None psj_GT.
Definition psj_stT : shst := fst (sym_runN_tok tfibsegs fsw_wr_tbl psl_K fs_Bx fs_Bspan psj_SH FUEL psj_ssT).
Definition psj_regsT : list sv := sr_set (sr_set ps_ret_regs 10%bv (SOff 60 0)) 11%bv (SOff 61 0).
Lemma psj_runT :
  sh_static_ok psl_K fs_Bx fs_Bspan psj_SH (ss_facts psj_ssT) (ss_mem psj_ssT) = true
  /\ sym_runN_tok tfibsegs fsw_wr_tbl psl_K fs_Bx fs_Bspan psj_SH FUEL psj_ssT
       = (psj_stT, TS_stopped (SR_load (Some 26%nat) 0))
  /\ sh_obls psj_stT = [] /\ sh_j psj_stT = 2%nat
  /\ ss_pc (sh_ss psj_stT) = PSJ_LOAD0 /\ ss_regs (sh_ss psj_stT) = psj_regsT
  /\ ss_resv (sh_ss psj_stT) = None.
Proof.
  split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; vm_compute; reflexivity.
Qed.
Lemma psj_on48 : YCeo.ss_atoms_on (fun n => negb (Nat.eqb n 48)) (sh_ss psj_stT) = true.
Proof. vm_compute; reflexivity. Qed.

(* ---- the cut: s[0] seated on atom 48, the stack window of the seven stores ---- *)
Definition psj_strc : YP09.region := YP09.mkRegion (Some 26%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 48 0))].
Definition psj_stk : YP09.region := YP09.mkRegion (Some 9%nat) 8 64 8 64 [].
Definition psj_stk7 : YP09.region := YP09.mkRegion (Some 9%nat) 8 64 8 64 psj_scs7.
Definition psj_ssC (lo hi : Z) : sstate :=
  mkSS PSJ_LOAD0 psj_regsT [psj_strc; psj_stk] None (mkFacts [(48%nat, mkAF lo hi 0)] [] []).
Definition psj_ssH (lo hi : Z) : sstate := fst (sym_run_toN tfibsegs fsw_wr_tbl FUEL PSL_HEAD (psj_ssC lo hi)).
(* the register file at PSL_HEAD (MEASURED): x10 .. x14 the five image addresses, x18 = c, x20 = s + 1,
   x21 = the frame + 32 (esc), x22 = the frame's shadow, x24 = x26 = s, x25 = 34 *)
Definition psj_regsH : list sv :=
  [SLit 0; SOff 1 0; SOff 2 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SOff 8 0; SOff 9 0;
   SLit 135776; SLit 134172; SLit 134176; SLit 134180; SLit 134184; SOff 15 0; SOff 16 0; SOff 17 0;
   SOff 48 0; SOff 19 0; SOff 26 1; SOff 24 32; SOff 47 0; SOff 32 0; SOff 26 0; SLit 34; SOff 26 0;
   SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
Lemma psj_runH : forall lo hi, psl_rng lo hi ->
  sym_run_toN tfibsegs fsw_wr_tbl FUEL PSL_HEAD (psj_ssC lo hi) = (psj_ssH lo hi, RS_running)
  /\ ss_pc (psj_ssH lo hi) = PSL_HEAD /\ ss_regs (psj_ssH lo hi) = psj_regsH
  /\ ss_mem (psj_ssH lo hi) = [psj_strc; psj_stk7] /\ ss_resv (psj_ssH lo hi) = None.
Proof.
  intros lo hi [(-> & ->) | [(-> & ->) | (-> & ->)]];
    (split; [vm_compute; reflexivity|]); (split; [vm_compute; reflexivity|]);
    (split; [vm_compute; reflexivity|]); (split; vm_compute; reflexivity).
Qed.
Definition psj_P (n : nat) : bool := negb (Nat.eqb n 48) && negb (Nat.eqb n 60) && negb (Nat.eqb n 61).
Lemma psj_stk7_on : YCeo.region_atoms_on psj_P psj_stk7 = true.
Proof. vm_compute; reflexivity. Qed.

(* ---- the empty string: the byte at s is the terminating zero ---- *)
Definition psj_ssCe : sstate :=
  add_cond (mkSS PSJ_LOAD0 psj_regsT [psj_strc] None (mkFacts [(48%nat, mkAF 0 0 0)] [] []))
    (mkAC BC_EQ (SOff 48 0) (SLit 0)).
Definition psj_ssAe : sstate := fst (sym_run_toN tfibsegs fsw_wr_tbl FUEL A_put psj_ssCe).
(* the register file at put #2's call in the empty arm, x18 (the zero byte) as the literal 0 *)
Definition psj_regsE0 : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set ps_ret_regs 1%bv (SLit PS_END_RET)) 10%bv (SOff 19 0))
    11%bv (SOff 26 0)) 12%bv (SLit 0)) 18%bv (SLit 0)) 20%bv (SOff 26 0).
Lemma psj_runE :
  sym_run_toN tfibsegs fsw_wr_tbl FUEL A_put psj_ssCe = (psj_ssAe, RS_running)
  /\ ss_pc psj_ssAe = A_put /\ ss_regs psj_ssAe = sr_set psj_regsE0 18%bv (SOff 48 0)
  /\ ss_mem psj_ssAe = [psj_strc] /\ ss_resv psj_ssAe = None.
Proof.
  split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|]. split; vm_compute; reflexivity.
Qed.
Lemma psj_regsE_set : sr_set (sr_set psj_regsE0 18%bv (SOff 48 0)) 18%bv (SLit 0) = psj_regsE0.
Proof. vm_compute; reflexivity. Qed.
Lemma psj_onE : YCeo.ss_atoms_on psj_P (mkSS A_put psj_regsE0 [] None (mkFacts [] [] [])) = true.
Proof. vm_compute; reflexivity. Qed.

(* ---- from PSL_END: the two reloaded slots, read-only, as esc - 32 (the frame) ---- *)
Definition psj_slots : YP09.region :=
  YP09.mkRegion (Some 9%nat) 8 24 0 0
    [YP09.mkChunk 8 (CVal 8 (SOff 21 (-32))); YP09.mkChunk 16 (CVal 8 (SOff 21 (-32)))].
Definition psj_ssE0 : sstate := mkSS PSL_END psl_regs [psj_slots] None (mkFacts [] [] []).
Definition psj_ssP2 : sstate := fst (sym_run_toN tfibsegs fsw_wr_tbl FUEL A_put psj_ssE0).
(* the register file at put #2's call after the loop: a2 = x24 - x26, x21 / x24 reloaded *)
Definition psj_put2_regs : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set psl_regs 1%bv (SLit PS_END_RET)) 10%bv (SOff 19 0))
    11%bv (SOff 26 0)) 12%bv (SAlu ALU_ADD (SOff 24 0) (SMd M_MUL (SOff 26 0) (SLit (-1)))))
    20%bv (SOff 24 0)) 21%bv (SOff 21 (-32))) 24%bv (SOff 21 (-32)).
Lemma psj_runP2 :
  sym_run_toN tfibsegs fsw_wr_tbl FUEL A_put psj_ssE0 = (psj_ssP2, RS_running)
  /\ ss_pc psj_ssP2 = A_put /\ ss_regs psj_ssP2 = psj_put2_regs
  /\ ss_mem psj_ssP2 = [psj_slots] /\ ss_resv psj_ssP2 = None.
Proof.
  split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|]. split; vm_compute; reflexivity.
Qed.

(* ---- from put #2's return: no region and no fact at all ---- *)
Definition psj_ssQ : sstate := mkSS PS_END_RET ps_ret_regs [] None (mkFacts [] [] []).
Definition psj_ssP3 : sstate := fst (sym_run_toN tfibsegs fsw_wr_tbl FUEL A_put psj_ssQ).
Definition psj_put3_regs : list sv :=
  sr_set (sr_set (sr_set (sr_set ps_ret_regs 1%bv (SLit PS_CLOSE_RET)) 10%bv (SOff 19 0)) 11%bv (SLit PS_Q1))
    12%bv (SLit 1).
Lemma psj_runP3 :
  sym_run_toN tfibsegs fsw_wr_tbl FUEL A_put psj_ssQ = (psj_ssP3, RS_running)
  /\ ss_pc psj_ssP3 = A_put /\ ss_regs psj_ssP3 = psj_put3_regs
  /\ ss_mem psj_ssP3 = [] /\ ss_resv psj_ssP3 = None.
Proof.
  split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|]. split; vm_compute; reflexivity.
Qed.

(* ================= small env, memory and arithmetic lemmas (never in a walk's context) ================= *)
Lemma psj_P_spec : forall n, psj_P n = true -> n <> 48%nat /\ n <> 60%nat /\ n <> 61%nat.
Proof.
  intros n H. unfold psj_P in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply negb_true_iff in H1, H2, H3. apply Nat.eqb_neq in H1, H2, H3. auto.
Qed.
Lemma psj_ew3 : forall E u1 u2 w n, n <> 48%nat -> n <> 60%nat -> n <> 61%nat ->
  ew (ewset (extK E psl_K [u1; u2]) 48 w) n = ew E n.
Proof.
  intros E u1 u2 w n H1 H2 H3. unfold psl_K. cbn [extK].
  rewrite (ew_ewset_other _ 48 w n H1), (ew_ewset_other _ 61 u2 n H3), (ew_ewset_other _ 60 u1 n H2).
  reflexivity.
Qed.
Lemma psj_agree3 : forall E u1 u2 w, YCeo.env_agree_on psj_P (ewset (extK E psl_K [u1; u2]) 48 w) E.
Proof.
  intros E u1 u2 w. split; [|reflexivity]. intros n Hn. destruct (psj_P_spec n Hn) as (H1 & H2 & H3).
  symmetry. exact (psj_ew3 E u1 u2 w n H1 H2 H3).
Qed.
Lemma psj_agree48 : forall E2 w, YCeo.env_agree_on (fun n => negb (Nat.eqb n 48)) E2 (ewset E2 48 w).
Proof.
  intros E2 w. split; [|reflexivity]. intros n Hn. apply ew_ewset_other. intros ->. cbn in Hn. discriminate Hn.
Qed.
Lemma psj_SOff_eq : forall E1 E2 n1 n2 k, ew E1 n1 = ew E2 n2 -> sv_denot E1 (SOff n1 k) = sv_denot E2 (SOff n2 k).
Proof. intros E1 E2 n1 n2 k H. apply bv_eq. rewrite !denot_SOff, H. reflexivity. Qed.
Lemma psj_SOff_m32 : forall E F, bv_unsigned (ew E 21) = F + 32 -> 0 <= F ->
  sv_denot E (SOff 21 (-32)) = Z_to_bv 64 F.
Proof.
  intros E F H HF. pose proof (u64_range (ew E 21)) as R. apply bv_eq. rewrite denot_SOff, H, wz by lia.
  replace (F + 32 + -32) with F by ring. apply zcanon_id. unfold M64. lia.
Qed.
Lemma psj_sub_val : forall E qe r, bv_unsigned (ew E 24) = qe -> bv_unsigned (ew E 26) = r ->
  sv_denot E (SAlu ALU_ADD (SOff 24 0) (SMd M_MUL (SOff 26 0) (SLit (-1)))) = Z_to_bv 64 (qe - r).
Proof.
  intros E qe r H24 H26. pose proof (u64_range (ew E 24)) as R24. pose proof (u64_range (ew E 26)) as R26.
  apply bv_eq. change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff 24 0) (SMd M_MUL (SOff 26 0) (SLit (-1))))))
    with (YP0e.U E (SAlu ALU_ADD (SOff 24 0) (SMd M_MUL (SOff 26 0) (SLit (-1))))).
  rewrite U_SAlu, U_SMd, !U_SOff, U_SLit, H24, H26. cbn [zalu_raw zmd_raw].
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus, zcanon, M64. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite !Z.add_0_r. rewrite (Z.mod_small qe) by lia. rewrite (Z.mod_small r) by lia.
  rewrite Zplus_mod_idemp_r. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
  replace (qe + r * (2 ^ 64 - 1)) with ((qe - r) + r * 2 ^ 64) by ring. rewrite Z.mod_add by lia.
  reflexivity.
Qed.
Lemma psj_rng_byte : forall lo hi c, psl_rng lo hi -> lo <= c <= hi -> 1 <= c < 2 ^ 8.
Proof. intros lo hi c [(-> & ->) | [(-> & ->) | (-> & ->)]] H; lia. Qed.
Lemma psj_mbyte_pt : forall (H : word -> bool) (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> mbyte tfibsegs (mrestrict H m') a = mbyte tfibsegs (mrestrict H m) a.
Proof. intros H m m' a E. unfold mbyte, mrestrict. rewrite E. reflexivity. Qed.
Lemma psj_writable_pt : forall (H : word -> bool) (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> writable_at tfibsegs (mrestrict H m) a ->
  writable_at tfibsegs (mrestrict H m') a.
Proof. intros H m m' a E Hw. unfold writable_at, wview, mrestrict in *. rewrite E. exact Hw. Qed.
Lemma psj_val_mem_pt : forall (H : word -> bool) (m m' : word -> option byte) a n v,
  (forall k, (k < n)%nat -> m' (Z_to_bv 64 (a + Z.of_nat k)) = m (Z_to_bv 64 (a + Z.of_nat k))) ->
  val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H m') a n v.
Proof. intros H m m' a n v E Hv k Hk. rewrite (psj_mbyte_pt H m m' _ (E k Hk)). exact (Hv k Hk). Qed.
(* an atom of the re-seated env (the machine's register file) read through the run's symbolic register *)
Lemma psj_ew_seat : forall (regs : bvmap 5 word) (E3 : env) (r : bv 5) nn n k v,
  Z.of_nat nn = bv_unsigned r -> YK11.getr regs r = sv_denot E3 (SOff n k) ->
  bv_unsigned (ew E3 n) + k = v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (ew (Ereg regs fs_extraT) nn) = v.
Proof.
  intros regs E3 r nn n k v Hn Hr Hv Hb. rewrite (ew_Ereg_nat regs fs_extraT nn r Hn), Hr, denot_SOff, Hv.
  apply zcanon_id. unfold M64. lia.
Qed.

Section J. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

(* the arithmetic of the opening stretch: the string byte, the stack window and the frame's shadow are apart *)
Lemma psj_sep : forall s sp1 sp0 STK F,
  4096 <= s -> s + 1 <= alloc_ceiling -> alloc_ceiling <= sp0 - STK -> sp0 - STK <= sp1 ->
  sp1 <= 2 ^ 47 - 88 -> 4096 <= F <= 2 ^ 47 - 64 ->
  ~ (SHADOW_OFF <= s < SHADOW_OFF + 17592186044416) ->
  s + 1 <= sp1 + 8 /\ (shadow_addr F + 8 <= s + 1 \/ s + 2 <= shadow_addr F) /\
  shadow_addr F + 8 <= sp1 + 8 /\ 0 <= shadow_addr F /\ shadow_addr F + 8 <= 2 ^ 64 /\
  0 <= s /\ s + 2 <= 2 ^ 64 /\ s <= 2 ^ 47 - 8 /\ 0 <= sp1 + 8 /\ sp1 + 88 <= 2 ^ 64.
Proof.
  intros s sp1 sp0 STK F H1 H2 H3 H4 H5 H6 H7. pose proof asan_consts as (C1 & _).
  unfold shadow_addr, SHADOW_OFF in *. Z.div_mod_to_equations. lia.
Qed.
Lemma psj_bd_open : forall c s F lo hi,
  lo <= c <= hi -> 4096 <= F <= 2 ^ 47 - 64 -> 4096 <= s -> s + 1 <= alloc_ceiling ->
  psl_bd c s (F + 32) (shadow_addr F) s lo hi.
Proof.
  intros c s F lo hi Hc HF Hs Hsc. pose proof asan_consts as (C1 & _).
  unfold psl_bd, shadow_addr, SHADOW_OFF. Z.div_mod_to_equations. lia.
Qed.
(* what the opening state's facts say of its atoms *)
Lemma psj_ret_atoms_ok : forall E L, facts_ok E (mkFacts (ps_ret_atoms L) [] []) ->
  2 ^ 46 <= bv_unsigned (ew E 9) <= 2 ^ 47 - 88 /\ 4096 <= bv_unsigned (ew E 24) <= 2 ^ 47 - 64 /\
  bv_unsigned (ew E 32) = SHADOW_OFF /\ 4096 <= bv_unsigned (ew E 26).
Proof.
  intros E L (HA & _). unfold ps_ret_atoms in HA. cbn [f_atoms atoms_ok] in HA. unfold afact_ok in HA.
  cbn [af_lo af_hi af_al2] in HA.
  destruct HA as (_ & (H9 & _) & (H24 & _) & _ & _ & (H32 & _) & (H26 & _) & _).
  unfold SHADOW_OFF in *. repeat split; lia.
Qed.

(* ---- two st_ok surgeries: re-seat a state on a new env / register file, and take the memory part of another ---- *)
Lemma psj_st_ok_reseat : forall E E' ss ss' ms,
  st_ok tfibsegs E ss ms -> ss_resv ss = None -> ss_pc ss' = ss_pc ss -> ss_resv ss' = None ->
  YP0l.regs_ok E' (ss_regs ss') (ms_regs ms) -> mem_ok tfibsegs E' (ms_mem ms) (ss_mem ss') ->
  facts_ok E' (ss_facts ss') -> st_ok tfibsegs E' ss' ms.
Proof.
  intros E E' ss ss' ms (H1 & H2 & H3 & H4 & H5 & H6 & _ & _ & _) Hr Hpc Hr' HR HM HF.
  rewrite Hr in H4. unfold st_ok. rewrite Hpc, Hr'.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  split; [exact H5|]. split; [exact H6|]. split; [exact HR|]. split; [exact HM | exact HF].
Qed.
Lemma psj_st_ok_merge : forall E ssA ssB msA msB,
  st_ok tfibsegs E ssA msA -> ss_resv ssA = None -> st_ok tfibsegs E ssB msB ->
  (forall x, ms_mem msA x = ms_mem msB x) ->
  st_ok tfibsegs E (mkSS (ss_pc ssA) (ss_regs ssA) (ss_mem ssB) None (ss_facts ssB)) msA.
Proof.
  intros E ssA ssB msA msB HA Hr HB Hm.
  apply (psj_st_ok_reseat E E ssA (mkSS (ss_pc ssA) (ss_regs ssA) (ss_mem ssB) None (ss_facts ssB)) msA
           HA Hr eq_refl eq_refl).
  - exact (st_ok_regs_ok tfibsegs E ssA msA HA).
  - destruct (st_ok_mem_ok tfibsegs E ssB msB HB) as (Hwf & Hok & Hpd).
    split; [exact Hwf|]. split; [|exact Hpd].
    rewrite Forall_forall in Hok |- *. intros r Hin.
    exact (psl_region_ok_eq E (ms_mem msB) (ms_mem msA) r Hm (Hok r Hin)).
  - exact (st_ok_facts_ok tfibsegs E ssB msB HB).
Qed.
Lemma psj_chunk_pt : forall E (m m' : word -> option byte) b ch,
  YP09.chunk_ok tfibsegs E m b ch ->
  (forall i, 0 <= i < YP09.c_len ch ->
     mbyte tfibsegs m' (b + YP09.c_off ch + i) = mbyte tfibsegs m (b + YP09.c_off ch + i)) ->
  YP09.chunk_ok tfibsegs E m' b ch.
Proof.
  intros E m m' b ch H Hm i Hi. destruct (H i Hi) as (bb & H1 & H2). exists bb. split; [exact H1|].
  rewrite (Hm i Hi). exact H2.
Qed.
(* a literal chunk read at another env, on a memory that agrees on its bytes *)
Lemma psj_chunk_lit_pt : forall E E' (m m' : word -> option byte) b off (w : N) z,
  YP09.chunk_ok tfibsegs E m b (YP09.mkChunk off (CVal w (SLit z))) ->
  (forall i, 0 <= i < YP09.c_len (YP09.mkChunk off (CVal w (SLit z))) ->
     mbyte tfibsegs m' (b + YP09.c_off (YP09.mkChunk off (CVal w (SLit z))) + i) =
     mbyte tfibsegs m (b + YP09.c_off (YP09.mkChunk off (CVal w (SLit z))) + i)) ->
  YP09.chunk_ok tfibsegs E' m' b (YP09.mkChunk off (CVal w (SLit z))).
Proof.
  intros E E' m m' b off w z H Hm. apply (psl_chunk_lit_env E E' m' b w z off).
  exact (psj_chunk_pt E m m' b _ H Hm).
Qed.
(* the frame's shadow byte at +4 (0xf8), as ps_fsh_chunks states it and as psl_sh_region states it *)
Lemma psj_chunk_f8 : forall E E' (m m' : word -> option byte) b,
  YP09.chunk_ok tfibsegs E m b (YP09.mkChunk 4 (CVal 1 (SLit 248))) ->
  mbyte tfibsegs m' (b + 4 + 0) = mbyte tfibsegs m (b + 4 + 0) ->
  YP09.chunk_ok tfibsegs E' m' b (YP09.mkChunk 4 (CVal 1 PSL_POIS)).
Proof.
  intros E E' m m' b H Hm i Hi. cbn in Hi. assert (i = 0) as -> by lia.
  destruct (H 0 ltac:(cbn; lia)) as (bb & H1 & H2). exists bb. split.
  - cbn [YP09.cbyte YP09.c_val YP09.c_off] in H1 |- *. unfold PSL_POIS.
    rewrite psl_lit_denot in H1 |- *. rewrite <- H1. f_equal. apply bv_eq. vm_compute. reflexivity.
  - cbn [YP09.c_off] in H2 |- *. rewrite Hm. exact H2.
Qed.

(* ================= 5. put #3's return IS the epilogue's state ================= *)
(* ps_ret_ss PS_CLOSE_RET L psj_scs0 [] and ps_epi_ss PS_CLOSE_RET have the same pc, register file, regions and
   reservation (MEASURED by vm_compute); they differ only in the facts: ps_ret_atoms L carries one more atom fact,
   (26, [4096, 2 ^ 47 - (L + 1)]) at its end. So the transfer is st_ok_facts on the shorter list. *)
Lemma psj_put3_close : forall L (E : env) ms,
  st_ok tfibsegs E (ps_ret_ss PS_CLOSE_RET L psj_scs0 []) ms -> st_ok tfibsegs E (ps_epi_ss PS_CLOSE_RET) ms.
Proof.
  intros L E ms HS.
  pose proof (st_ok_facts_ok tfibsegs E _ ms HS) as (HA & _).
  unfold ps_ret_ss, ps_ret_atoms in HA. cbn [ss_facts f_atoms atoms_ok] in HA.
  destruct HA as (A8 & A9 & A24 & A47 & A46 & A32 & _).
  exact (st_ok_facts tfibsegs E _ ms (ss_facts (ps_epi_ss PS_CLOSE_RET)) HS
    (conj (conj A8 (conj A9 (conj A24 (conj A47 (conj A46 (conj A32 I)))))) (conj I I))).
Qed.

(* ================= 4. from put #2's return to put #3's call (the closing quote) ================= *)
(* MEASURED: the stretch needs no region and no fact (psj_runP3), so it holds for ANY slot list scs and any extra
   regions rs (in particular scs1 and rs = []); the call-site state keeps every region and fact of the return state. *)
Lemma psj_put2_put3 : forall L scs rs o (E : env) ms STK sp0 FP ly S W0 mem0 md0 own lyc Sc U
    (W : world tfibsegs) mdc k (Q : world tfibsegs -> config -> Prop),
  st_ok tfibsegs E (ps_ret_ss PS_END_RET L scs rs) (restrict (w_H W) ms) ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison U (ms_mem ms)) mdc k ->
  ARU tfibsegs B lyc Sc U W (ms_mem ms) mdc ->
  bv_unsigned (ew E 19) = o ->
  (forall ms' mat',
     st_ok tfibsegs E (mkSS A_put psj_put3_regs (ps_ret_regions scs rs) None (mkFacts (ps_ret_atoms L) [] []))
       (restrict (w_H W) ms') ->
     ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison U (ms_mem ms'))
       (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
     ARU tfibsegs B lyc Sc U W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) ->
     (forall x, ms_mem ms' x = ms_mem ms x) ->
     YK11.getr (ms_regs ms') 1%bv = Z_to_bv 64 PS_CLOSE_RET -> YK11.getr (ms_regs ms') 10%bv = Z_to_bv 64 o ->
     YK11.getr (ms_regs ms') 11%bv = Z_to_bv 64 PS_Q1 -> YK11.getr (ms_regs ms') 12%bv = Z_to_bv 64 1 ->
     SRr tfibsegs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros L scs rs o E ms STK sp0 FP ly S W0 mem0 md0 own lyc Sc U W mdc k Q HS HJ HARU E19 KONT.
destruct psj_runP3 as (HRUN & HPC & HRG & HMEM & HRV).
assert (HQ : st_ok tfibsegs E psj_ssQ (restrict (w_H W) ms)).
{ pose proof (st_ok_submem tfibsegs E _ _ [] HS (submem_nil _) eq_refl) as HX.
  exact (st_ok_facts tfibsegs E _ _ (mkFacts [] [] []) HX (conj I (conj I I))). }
eapply (fsw_run_to_AJU B fsw_wr_tbl fsw_wr_tbl_ok W FUEL A_put E psj_ssQ psj_ssP3 RS_running ms
          STK sp0 FP ly S W0 mem0 md0 own lyc Sc U mdc k Q);
  [exact HQ | exact HRUN | exact I | exact HARU | exact HJ | apply awr_ok_nil | ].
intros ms2 mat2 HS2 HJ2 HARU2 HF2 HFr2 HG2.
assert (MEQ : forall x, ms_mem ms2 x = ms_mem ms x)
  by exact (psl_frame_ro E [] (ms_mem ms) (ms_mem ms2) (Forall_nil _) HF2).
assert (HM : st_ok tfibsegs E (mkSS A_put psj_put3_regs (ps_ret_regions scs rs) None (mkFacts (ps_ret_atoms L) [] []))
               (restrict (w_H W) ms2)).
{ pose proof (psj_st_ok_merge E psj_ssP3 _ (restrict (w_H W) ms2) (restrict (w_H W) ms) HS2 HRV HS
    ltac:(intros x; cbn [ms_mem restrict]; unfold mrestrict; rewrite MEQ; reflexivity)) as HX.
  rewrite HPC, HRG in HX. exact HX. }
assert (R1 : YK11.getr (ms_regs ms2) 1%bv = Z_to_bv 64 PS_CLOSE_RET)
  by exact (fsw_reg_lit _ E _ ms2 1%bv PS_CLOSE_RET HM ltac:(vm_compute; reflexivity)
              ltac:(clear; unfold PS_CLOSE_RET; lia)).
assert (R10 : YK11.getr (ms_regs ms2) 10%bv = Z_to_bv 64 o).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ ms2 10%bv HM).
  change (sr_get (ss_regs (mkSS A_put psj_put3_regs (ps_ret_regions scs rs) None (mkFacts (ps_ret_atoms L) [] []))) 10%bv)
    with (SOff 19 0).
  rewrite fsw_SOff0, <- E19. symmetry. apply Z_to_bv_bv_unsigned. }
assert (R11 : YK11.getr (ms_regs ms2) 11%bv = Z_to_bv 64 PS_Q1)
  by exact (fsw_reg_lit _ E _ ms2 11%bv PS_Q1 HM ltac:(vm_compute; reflexivity) ltac:(clear; unfold PS_Q1; lia)).
assert (R12 : YK11.getr (ms_regs ms2) 12%bv = Z_to_bv 64 1)
  by exact (fsw_reg_lit _ E _ ms2 12%bv 1 HM ltac:(vm_compute; reflexivity) ltac:(clear; lia)).
exact (KONT ms2 mat2 HM HJ2 HARU2 MEQ R1 R10 R11 R12).
Qed.

(* ================= 3. from PSL_END to put #2's call (the run of bytes) ================= *)
(* The loop's end state (a Theorem Labs lane's psl_last / psl_scan) has the register file psl_regs at PSL_END with ANY regions rs
   and facts G ([psl_sh_region] and psl_G); its env reads ew 24 = qe (the terminating zero's address),
   ew 26 = r, ew 19 = o, ew 21 = esc = the frame + 32. The stretch reloads x24 := [sp1 + 8] and x21 := [sp1 + 16];
   both slots hold the frame F (psj_scs7's chunks at +8 / +16, written by the opening stretch). MEASURED: no write,
   no fact needed. *)
Lemma psj_end_put2 : forall rs G sp1 F qe r o (E : env) ms STK sp0 FP ly S W0 mem0 md0 own lyc Sc U
    (W : world tfibsegs) mdc k (Q : world tfibsegs -> config -> Prop),
  st_ok tfibsegs E (mkSS PSL_END psl_regs rs None G) (restrict (w_H W) ms) ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison U (ms_mem ms)) mdc k ->
  ARU tfibsegs B lyc Sc U W (ms_mem ms) mdc ->
  bv_unsigned (ew E 9) = sp1 -> bv_unsigned (ew E 21) = F + 32 -> bv_unsigned (ew E 24) = qe ->
  bv_unsigned (ew E 26) = r -> bv_unsigned (ew E 19) = o ->
  0 <= sp1 <= 2 ^ 47 -> 0 <= F ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (sp1 + 8) 8 F ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (sp1 + 16) 8 F ->
  (forall ms' mat',
     st_ok tfibsegs E (mkSS A_put psj_put2_regs rs None G) (restrict (w_H W) ms') ->
     ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison U (ms_mem ms'))
       (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
     ARU tfibsegs B lyc Sc U W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) ->
     (forall x, ms_mem ms' x = ms_mem ms x) ->
     YK11.getr (ms_regs ms') 1%bv = Z_to_bv 64 PS_END_RET -> YK11.getr (ms_regs ms') 10%bv = Z_to_bv 64 o ->
     YK11.getr (ms_regs ms') 11%bv = Z_to_bv 64 r -> YK11.getr (ms_regs ms') 12%bv = Z_to_bv 64 (qe - r) ->
     YK11.getr (ms_regs ms') 21%bv = Z_to_bv 64 F -> YK11.getr (ms_regs ms') 24%bv = Z_to_bv 64 F ->
     SRr tfibsegs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros rs G sp1 F qe r o E ms STK sp0 FP ly S W0 mem0 md0 own lyc Sc U W mdc k Q
  HS HJ HARU E9 E21 E24 E26 E19 Hsp1 HF0 HV8 HV16 KONT.
destruct psj_runP2 as (HRUN & HPC & HRG & HMEM & HRV).
assert (D21 : sv_denot E (SOff 21 (-32)) = Z_to_bv 64 F) by exact (psj_SOff_m32 E F E21 HF0).
assert (HF64 : 0 <= F < 2 ^ (8 * Z.of_N 8)).
{ pose proof (u64_range (ew E 21)) as R. rewrite E21 in R. change (8 * Z.of_N 8) with 64. clear - R HF0. lia. }
assert (HSL : region_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms)) psj_slots).
{ unfold psj_slots, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9. split; [clear - Hsp1; lia|]. split; [clear - Hsp1; lia|].
  split; [intros oo Hoo; exfalso; clear - Hoo; lia|].
  constructor; [|constructor; [|constructor]].
  - exact (chunk_ok_val tfibsegs E _ sp1 8 8 (SOff 21 (-32)) F D21 HF64 ltac:(clear; cbn; lia) HV8).
  - exact (chunk_ok_val tfibsegs E _ sp1 16 8 (SOff 21 (-32)) F D21 HF64 ltac:(clear; cbn; lia) HV16). }
assert (HE0 : st_ok tfibsegs E psj_ssE0 (restrict (w_H W) ms)).
{ pose proof (st_ok_submem tfibsegs E _ _ [] HS (submem_nil _) eq_refl) as HX.
  pose proof (st_ok_facts tfibsegs E _ _ (mkFacts [] [] []) HX (conj I (conj I I))) as HX1.
  pose proof (st_ok_add_region' tfibsegs E _ (restrict (w_H W) ms) psj_slots HX1 ltac:(vm_compute; reflexivity))
    as HX2.
  cbn [ms_mem restrict] in HX2. exact (HX2 HSL I). }
eapply (fsw_run_to_AJU B fsw_wr_tbl fsw_wr_tbl_ok W FUEL A_put E psj_ssE0 psj_ssP2 RS_running ms
          STK sp0 FP ly S W0 mem0 md0 own lyc Sc U mdc k Q);
  [exact HE0 | exact HRUN | exact I | exact HARU | exact HJ
  | apply awr_ok_cons_ro; [cbn; apply Z.le_refl | apply awr_ok_nil] | ].
intros ms2 mat2 HS2 HJ2 HARU2 HF2 HFr2 HG2.
assert (MEQ : forall x, ms_mem ms2 x = ms_mem ms x).
{ apply (psl_frame_ro E [psj_slots] (ms_mem ms) (ms_mem ms2));
    [constructor; [cbn; apply Z.le_refl | constructor] | exact HF2]. }
assert (HM : st_ok tfibsegs E (mkSS A_put psj_put2_regs rs None G) (restrict (w_H W) ms2)).
{ pose proof (psj_st_ok_merge E psj_ssP2 _ (restrict (w_H W) ms2) (restrict (w_H W) ms) HS2 HRV HS
    ltac:(intros x; cbn [ms_mem restrict]; unfold mrestrict; rewrite MEQ; reflexivity)) as HX.
  rewrite HPC, HRG in HX. exact HX. }
set (ssM := mkSS A_put psj_put2_regs rs None G) in HM.
assert (RG : forall rr, YK11.getr (ms_regs ms2) rr = sv_denot E (sr_get psj_put2_regs rr))
  by (intros rr; exact (st_ok_restrict_reg tfibsegs (w_H W) E ssM ms2 rr HM)).
assert (R1 : YK11.getr (ms_regs ms2) 1%bv = Z_to_bv 64 PS_END_RET)
  by exact (fsw_reg_lit _ E ssM ms2 1%bv PS_END_RET HM ltac:(vm_compute; reflexivity)
              ltac:(clear; unfold PS_END_RET; lia)).
assert (R10 : YK11.getr (ms_regs ms2) 10%bv = Z_to_bv 64 o).
{ rewrite (RG 10%bv). change (sr_get psj_put2_regs 10%bv) with (SOff 19 0).
  rewrite fsw_SOff0, <- E19. symmetry. apply Z_to_bv_bv_unsigned. }
assert (R11 : YK11.getr (ms_regs ms2) 11%bv = Z_to_bv 64 r).
{ rewrite (RG 11%bv). change (sr_get psj_put2_regs 11%bv) with (SOff 26 0).
  rewrite fsw_SOff0, <- E26. symmetry. apply Z_to_bv_bv_unsigned. }
assert (R12 : YK11.getr (ms_regs ms2) 12%bv = Z_to_bv 64 (qe - r)).
{ rewrite (RG 12%bv).
  change (sr_get psj_put2_regs 12%bv) with (SAlu ALU_ADD (SOff 24 0) (SMd M_MUL (SOff 26 0) (SLit (-1)))).
  exact (psj_sub_val E qe r E24 E26). }
assert (R21 : YK11.getr (ms_regs ms2) 21%bv = Z_to_bv 64 F).
{ rewrite (RG 21%bv). change (sr_get psj_put2_regs 21%bv) with (SOff 21 (-32)). exact D21. }
assert (R24 : YK11.getr (ms_regs ms2) 24%bv = Z_to_bv 64 F).
{ rewrite (RG 24%bv). change (sr_get psj_put2_regs 24%bv) with (SOff 21 (-32)). exact D21. }
exact (KONT ms2 mat2 HM HJ2 HARU2 MEQ R1 R10 R11 R12 R21 R24).
Qed.

(* ================= the shared first stage of the two opening arms ================= *)
(* From the opening put's return, s[0]'s inline shadow check as ONE token run (SH = the string's one-byte entry;
   every writable region dropped first, they are not covered and sh_static_ok is false with them), stopping at the
   data load PSJ_LOAD0 0x85bfc. The token run's one region is read-only, so the memory is unchanged. *)
Lemma psj_tok : forall L s (E : env) ms STK sp0 FP ly S W0 mem0 md0 own lyc Sc U
    (W : world tfibsegs) mdc k (Q : world tfibsegs -> config -> Prop),
  st_ok tfibsegs E (ps_ret_ss PS_OPEN_RET L psj_scs0 [ps_str_region L]) (restrict (w_H W) ms) ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison U (ms_mem ms)) mdc k ->
  ARU tfibsegs B lyc Sc U W (ms_mem ms) mdc ->
  0 <= L -> bv_unsigned (ew E 26) = s ->
  s + 1 <= alloc_ceiling -> ~ (SHADOW_OFF <= s < SHADOW_OFF + 17592186044416) ->
  range_addressable (aview tfibsegs (w_H W) (ms_mem ms)) SHADOW_OFF s 1 ->
  (forall u1 u2 ms1 mat1,
     st_ok tfibsegs (extK E psl_K [u1; u2]) (sh_ss psj_stT) (restrict (w_H W) ms1) ->
     ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison U (ms_mem ms1))
       (with_vm_backing (m_vm_lazy mdc) mat1 mdc) k ->
     ARU tfibsegs B lyc Sc U W (ms_mem ms1) (with_vm_backing (m_vm_lazy mdc) mat1 mdc) ->
     (forall x, ms_mem ms1 x = ms_mem ms x) ->
     SRr tfibsegs W (mkCfg ms1 (with_vm_backing (m_vm_lazy mdc) mat1 mdc)) Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros L s E ms STK sp0 FP ly S W0 mem0 md0 own lyc Sc U W mdc k Q HS HJ HARU HL E26 Hsceil HAPP HRA KONT.
pose proof (psj_ret_atoms_ok E L (st_ok_facts_ok tfibsegs E _ _ HS)) as (_ & _ & H32u & Hs4096).
rewrite E26 in Hs4096.
pose proof asan_consts as (C1 & _).
assert (Hs47 : 4096 <= s <= 2 ^ 47 - 8) by (clear - Hs4096 Hsceil C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite <- H32u; symmetry; apply Z_to_bv_bv_unsigned).
assert (E26' : ew E 26 = Z_to_bv 64 s) by (rewrite <- E26; symmetry; apply Z_to_bv_bv_unsigned).
destruct psj_runT as (HSTAT & HRUNT & HOBL & HJJ & _ & _ & _).
(* the token run's state: the string's first byte only, the facts of 26 and 32 *)
assert (HT : st_ok tfibsegs E psj_ssT (restrict (w_H W) ms)).
{ pose proof (st_ok_submem tfibsegs E _ _ [psj_str0] HS
    ltac:(unfold ps_ret_ss, ps_ret_regions; cbn [ss_mem];
          do 5 apply submem_drop; apply submem_keep; [|apply submem_nil];
          unfold subregion, psj_str0, ps_str_region;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
          split; [reflexivity|]; split; [apply Z.le_refl|]; split; [clear - HL; lia|];
          split; [left; apply Z.le_refl | intros cc []])
    ltac:(vm_compute; reflexivity)) as HX.
  refine (st_ok_facts tfibsegs E _ _ psj_GT HX _).
  split; [|split; exact I]. cbn [psj_GT f_atoms atoms_ok].
  split; [exact (psl_afact E 26 s 4096 (2 ^ 47 - 8) E26 Hs47)|].
  split; [exact (psl_afact E 32 SHADOW_OFF SHADOW_OFF SHADOW_OFF H32u (conj (Z.le_refl _) (Z.le_refl _)))|exact I]. }
assert (SHOK : sh_ok tfibsegs fs_Bx psj_SH E (mrestrict (w_H W) (ms_mem ms))).
{ unfold psj_SH. constructor; [|constructor].
  apply (shent_ok_of_range tfibsegs (w_H W) (ms_mem ms) E fs_Bx 26%nat s 1 s 0 1 HRA).
  - unfold fs_Bx. apply (U_atom E 32 SHADOW_OFF E32). clear; unfold SHADOW_OFF; lia.
  - apply (U_atom E 26 s E26'). clear - Hs47; lia.
  - clear; lia.
  - clear; lia.
  - intros x Hx. cbn [Z.min Z.max] in Hx. assert (x = s) as -> by (clear - Hx; lia). exact HAPP. }
eapply (fsw_run_tok_AJU B fsw_wr_tbl fsw_wr_tbl_ok W FUEL E psl_K fs_Bx fs_Bspan psj_SH
          psj_ssT psj_stT (TS_stopped (SR_load (Some 26%nat) 0)) ms
          STK sp0 FP ly S W0 mem0 md0 own lyc Sc U mdc k Q);
  [exact HT | exact SHOK | exact HSTAT | exact HRUNT | exact I | exact HARU | exact HJ
  | rewrite HOBL; apply Forall_nil
  | cbn [psj_ssT ss_mem]; apply awr_ok_cons_ro; [cbn; apply Z.le_refl | apply awr_ok_nil] | ].
intros ws ms1 mat1 Hlen HS1 Hsh1 HJ1 HARU1 HF1 HFr1 HG1.
rewrite HJJ in Hlen.
destruct ws as [|u1 ws]; [discriminate Hlen|].
destruct ws as [|u2 ws]; [discriminate Hlen|].
destruct ws as [|u3 ws]; [|discriminate Hlen]. clear Hlen.
assert (MEQ1 : forall x, ms_mem ms1 x = ms_mem ms x).
{ apply (psl_frame_ro E [psj_str0] (ms_mem ms) (ms_mem ms1));
    [constructor; [cbn; apply Z.le_refl | constructor] | exact HF1]. }
exact (KONT u1 u2 ms1 mat1 HS1 HJ1 HARU1 MEQ1).
Qed.

(* ================= 2. the EMPTY string: from the opening put's return to put #2's call ================= *)
(* The byte at s is the terminating zero: s[0]'s inline shadow check (psj_tok), the cut at its data load, the byte
   seated as 0 (the engine does not decide `beqz` from a singleton range, so the walk adds the condition), then the
   run to put #2's call (MEASURED: A_put, a0 = o, a1 = s, a2 = 0, ra = PS_END_RET 0x85d88; no write; the loop is
   never entered). The call-site state is the return state's own regions and facts in the SAME env. *)
Lemma psj_open_empty : forall L s o (E : env) ms STK sp0 FP ly S W0 mem0 md0 own lyc Sc U
    (W : world tfibsegs) mdc k (Q : world tfibsegs -> config -> Prop),
  st_ok tfibsegs E (ps_ret_ss PS_OPEN_RET L psj_scs0 [ps_str_region L]) (restrict (w_H W) ms) ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison U (ms_mem ms)) mdc k ->
  ARU tfibsegs B lyc Sc U W (ms_mem ms) mdc ->
  0 <= L -> bv_unsigned (ew E 26) = s -> bv_unsigned (ew E 19) = o ->
  (* the string: its first byte is the terminating zero *)
  s + 1 <= alloc_ceiling -> ~ (SHADOW_OFF <= s < SHADOW_OFF + 17592186044416) ->
  range_addressable (aview tfibsegs (w_H W) (ms_mem ms)) SHADOW_OFF s 1 ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) s 1 0 ->
  (forall ms' mat',
     st_ok tfibsegs E (mkSS A_put psj_regsE0 (ps_ret_regions psj_scs0 [ps_str_region L]) None
                         (mkFacts (ps_ret_atoms L) [] [])) (restrict (w_H W) ms') ->
     ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison U (ms_mem ms'))
       (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
     ARU tfibsegs B lyc Sc U W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) ->
     (forall x, ms_mem ms' x = ms_mem ms x) ->
     YK11.getr (ms_regs ms') 1%bv = Z_to_bv 64 PS_END_RET -> YK11.getr (ms_regs ms') 10%bv = Z_to_bv 64 o ->
     YK11.getr (ms_regs ms') 11%bv = Z_to_bv 64 s -> YK11.getr (ms_regs ms') 12%bv = Z_to_bv 64 0 ->
     SRr tfibsegs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros L s o E ms STK sp0 FP ly S W0 mem0 md0 own lyc Sc U W mdc k Q
  HS HJ HARU HL E26 E19 Hsceil HAPP HRA HVAL KONT.
pose proof (psj_ret_atoms_ok E L (st_ok_facts_ok tfibsegs E _ _ HS)) as (_ & _ & _ & Hs4096).
rewrite E26 in Hs4096.
pose proof asan_consts as (C1 & _).
assert (Hs47 : 4096 <= s <= 2 ^ 47 - 8) by (clear - Hs4096 Hsceil C1; lia).
assert (E26' : ew E 26 = Z_to_bv 64 s) by (rewrite <- E26; symmetry; apply Z_to_bv_bv_unsigned).
destruct psj_runT as (_ & _ & _ & _ & HPCT & HRGT & HRVT).
destruct psj_runE as (HRUNE & HPCE & HRGE & HMEME & HRVE).
apply (psj_tok L s E ms STK sp0 FP ly S W0 mem0 md0 own lyc Sc U W mdc k Q HS HJ HARU HL E26 Hsceil HAPP HRA).
intros u1 u2 ms1 mat1 HS1 HJ1 HARU1 MEQ1.
(* ---- the cut: the byte 0 seated on atom 48 ---- *)
set (E2 := extK E psl_K [u1; u2]) in *.
set (E3 := ewset E2 48 (Z_to_bv 64 0)).
assert (E3_48 : ew E3 48 = Z_to_bv 64 0) by (unfold E3; apply ew_ewset_same).
assert (EW26 : ew E3 26 = ew E 26)
  by exact (psj_ew3 E u1 u2 _ 26 ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)).
assert (HS3 : st_ok tfibsegs E3 (sh_ss psj_stT) (restrict (w_H W) ms1))
  by exact (YCeo.st_ok_agree_on tfibsegs _ E2 E3 _ _ HS1 (psj_agree48 E2 _) psj_on48).
assert (HSTR : region_ok tfibsegs E3 (mrestrict (w_H W) (ms_mem ms1)) psj_strc).
{ unfold psj_strc, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite EW26, E26. split; [clear - Hs47; lia|]. split; [clear - Hs47; lia|].
  split; [intros oo Hoo; exfalso; clear - Hoo; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val tfibsegs E3 _ s 0 1 (SOff 48 0) 0);
    [rewrite fsw_SOff0, E3_48; reflexivity | clear; cbn; lia | clear; cbn; lia|].
  intros i Hi. rewrite (psj_mbyte_pt (w_H W) (ms_mem ms) (ms_mem ms1) _ (MEQ1 _)).
  rewrite Z.add_0_r. exact (HVAL i Hi). }
assert (HSC : st_ok tfibsegs E3 psj_ssCe (restrict (w_H W) ms1)).
{ pose proof (st_ok_submem tfibsegs E3 (sh_ss psj_stT) (restrict (w_H W) ms1) [] HS3 (submem_nil _) eq_refl) as HX1.
  pose proof (st_ok_add_region' tfibsegs E3 _ (restrict (w_H W) ms1) psj_strc HX1 ltac:(vm_compute; reflexivity))
    as HX2.
  cbn [ms_mem restrict] in HX2.
  pose proof (HX2 HSTR I) as HX3.
  pose proof (st_ok_facts tfibsegs E3 _ _ (mkFacts [(48%nat, mkAF 0 0 0)] [] []) HX3
    (conj (conj (psl_afact E3 48 0 0 0 ltac:(rewrite E3_48; reflexivity) ltac:(clear; lia)) I) (conj I I))) as HX4.
  pose proof (st_ok_add_cond tfibsegs E3 _ _ BC_EQ (SOff 48 0) (SLit 0) HX4
    ltac:(rewrite fsw_SOff0, E3_48, psl_lit_denot; vm_compute; reflexivity)) as HX5.
  unfold psj_ssCe. rewrite HPCT, HRGT, HRVT in HX5. exact HX5. }
(* ---- the run to put #2's call ---- *)
eapply (fsw_run_to_AJU B fsw_wr_tbl fsw_wr_tbl_ok W FUEL A_put E3 psj_ssCe psj_ssAe RS_running ms1
          STK sp0 FP ly S W0 mem0 md0 own lyc Sc U _ k Q);
  [exact HSC | exact HRUNE | exact I | exact HARU1 | exact HJ1
  | unfold psj_ssCe, add_cond; cbn [ss_mem]; apply awr_ok_cons_ro; [cbn; apply Z.le_refl | apply awr_ok_nil] | ].
intros ms2 mat2 HS2 HJ2 HARU2 HF2 HFr2 HG2.
rewrite wvb_collapse in HJ2. rewrite wvb_collapse in HARU2. rewrite wvb_collapse.
assert (MEQ : forall x, ms_mem ms2 x = ms_mem ms x).
{ intros x. rewrite <- (MEQ1 x).
  apply (psl_frame_ro E3 [psj_strc] (ms_mem ms1) (ms_mem ms2));
    [constructor; [cbn; apply Z.le_refl | constructor] | exact HF2]. }
(* ---- back to the env E: x18 is the literal 0, then the state names no atom 48 / 60 / 61 ---- *)
assert (HA : st_ok tfibsegs E (mkSS A_put psj_regsE0 [] None (mkFacts [] [] [])) (restrict (w_H W) ms2)).
{ pose proof (st_ok_submem tfibsegs E3 _ _ [] HS2 (submem_nil _) eq_refl) as HX1.
  pose proof (st_ok_facts tfibsegs E3 _ _ (mkFacts [] [] []) HX1 (conj I (conj I I))) as HX2.
  rewrite HPCE, HRGE, HRVE in HX2.
  pose proof (st_ok_set_reg tfibsegs E3 _ _ 18%bv (SLit 0) HX2 ltac:(discriminate)
    ltac:(cbn [ms_regs restrict];
          rewrite (st_ok_restrict_reg tfibsegs (w_H W) E3 psj_ssAe ms2 18%bv HS2), HRGE;
          change (sr_get (sr_set psj_regsE0 18%bv (SOff 48 0)) 18%bv) with (SOff 48 0);
          rewrite fsw_SOff0, E3_48, psl_lit_denot; reflexivity)) as HX3.
  change (st_ok tfibsegs E3 (mkSS A_put (sr_set (sr_set psj_regsE0 18%bv (SOff 48 0)) 18%bv (SLit 0)) [] None
            (mkFacts [] [] [])) (restrict (w_H W) ms2)) in HX3.
  rewrite psj_regsE_set in HX3.
  exact (YCeo.st_ok_agree_on tfibsegs _ E3 E _ _ HX3 (psj_agree3 E u1 u2 _) psj_onE). }
assert (HM : st_ok tfibsegs E (mkSS A_put psj_regsE0 (ps_ret_regions psj_scs0 [ps_str_region L]) None
                                 (mkFacts (ps_ret_atoms L) [] [])) (restrict (w_H W) ms2))
  by exact (psj_st_ok_merge E _ _ (restrict (w_H W) ms2) (restrict (w_H W) ms) HA eq_refl HS
              ltac:(intros x; cbn [ms_mem restrict]; unfold mrestrict; rewrite MEQ; reflexivity)).
set (ssM := mkSS A_put psj_regsE0 (ps_ret_regions psj_scs0 [ps_str_region L]) None (mkFacts (ps_ret_atoms L) [] []))
  in HM.
assert (R1 : YK11.getr (ms_regs ms2) 1%bv = Z_to_bv 64 PS_END_RET)
  by exact (fsw_reg_lit _ E ssM ms2 1%bv PS_END_RET HM ltac:(vm_compute; reflexivity)
              ltac:(clear; unfold PS_END_RET; lia)).
assert (R10 : YK11.getr (ms_regs ms2) 10%bv = Z_to_bv 64 o).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ssM ms2 10%bv HM).
  change (sr_get (ss_regs ssM) 10%bv) with (SOff 19 0).
  rewrite fsw_SOff0, <- E19. symmetry. apply Z_to_bv_bv_unsigned. }
assert (R11 : YK11.getr (ms_regs ms2) 11%bv = Z_to_bv 64 s).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ssM ms2 11%bv HM).
  change (sr_get (ss_regs ssM) 11%bv) with (SOff 26 0). rewrite fsw_SOff0. exact E26'. }
assert (R12 : YK11.getr (ms_regs ms2) 12%bv = Z_to_bv 64 0)
  by exact (fsw_reg_lit _ E ssM ms2 12%bv 0 HM ltac:(vm_compute; reflexivity) ltac:(clear; lia)).
exact (KONT ms2 mat2 HM HJ2 HARU2 MEQ R1 R10 R11 R12).
Qed.

(* ================= 1. the NON-EMPTY plain string: from the opening put's return to the loop head ============== *)
(* psj_tok, the cut at s[0]'s data load (the byte c seated on atom 48 from val_mem, fact [lo, hi] of psl_rng), then
   the plain run to PSL_HEAD 0x85c58 (MEASURED: RS_running in all three ranges; the stretch writes the seven words
   psj_scs7 at sp1 + 8 .. sp1 + 64 and nothing else). At the head the state is re-seated on the machine's register
   file (E' = Ereg regs fs_extraT, atom 32 = the shadow base): psl_head lo hi with q = r = s, esc = F + 32,
   shF = shadow_addr F. psl_sh_region's writability and its 0xf8 byte come from the return state's frame-shadow
   region (atom 47), whose bytes the stretch does not touch. *)
Lemma psj_open_head : forall L lo hi c s o F sp1 (E : env) ms STK sp0 FP ly S W0 mem0 md0 own lyc Sc U
    (W : world tfibsegs) mdc k (Q : world tfibsegs -> config -> Prop),
  st_ok tfibsegs E (ps_ret_ss PS_OPEN_RET L psj_scs0 [ps_str_region L]) (restrict (w_H W) ms) ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison U (ms_mem ms)) mdc k ->
  ARU tfibsegs B lyc Sc U W (ms_mem ms) mdc ->
  0 <= L -> bv_unsigned (ew E 26) = s -> bv_unsigned (ew E 19) = o -> bv_unsigned (ew E 24) = F ->
  bv_unsigned (ew E 47) = shadow_addr F -> bv_unsigned (ew E 9) = sp1 ->
  (* the stack window of the seven stores lies in the journal's window *)
  sp0 - STK <= sp1 -> sp1 + 88 <= sp0 ->
  (* the string: its first byte c is plain (one of the three ranges) *)
  psl_rng lo hi -> lo <= c <= hi ->
  s + 1 <= alloc_ceiling -> ~ (SHADOW_OFF <= s < SHADOW_OFF + 17592186044416) ->
  range_addressable (aview tfibsegs (w_H W) (ms_mem ms)) SHADOW_OFF s 1 ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) s 1 c ->
  (forall ms' mat' E',
     st_ok tfibsegs E' (psl_head lo hi) (restrict (w_H W) ms') ->
     ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison U (ms_mem ms'))
       (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
     ARU tfibsegs B lyc Sc U W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) ->
     psl_at E' c s (F + 32) (shadow_addr F) o s ->
     psl_bd c s (F + 32) (shadow_addr F) s lo hi ->
     (forall n, In n [2%nat; 3%nat; 4%nat; 8%nat; 9%nat; 27%nat] -> ew E' n = ew E n) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 8 <= a < sp1 + 64) ->
        ms_mem ms' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) ->
     Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms')) sp1) psj_scs1 ->
     val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms')) (sp1 + 8) 8 F ->
     val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms')) (sp1 + 16) 8 F ->
     SRr tfibsegs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros L lo hi c s o F sp1 E ms STK sp0 FP ly S W0 mem0 md0 own lyc Sc U W mdc k Q
  HS HJ HARU HL E26 E19 E24 E47 E9 Hwin Hsp88 Hrng Hc Hsceil HAPP HRA HVAL KONT.
pose proof (psj_ret_atoms_ok E L (st_ok_facts_ok tfibsegs E _ _ HS)) as (H9r & H24r & H32u & Hs4096).
rewrite E9 in H9r. rewrite E24 in H24r. rewrite E26 in Hs4096.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & _).
pose proof (psj_sep s sp1 sp0 STK F Hs4096 Hsceil ltac:(clear - Hceil Hslo; lia) Hwin ltac:(clear - H9r; lia)
  H24r HAPP) as (SP1 & SP2 & SP3 & SP4 & SP5 & SP6 & SP7 & SP8 & SP9 & SP10).
pose proof (psj_rng_byte lo hi c Hrng Hc) as Hc8.
pose proof (psj_bd_open c s F lo hi Hc H24r Hs4096 Hsceil) as HBD.
assert (Hs47 : 4096 <= s <= 2 ^ 47 - 8) by (clear - Hs4096 SP8; lia).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite <- H32u; symmetry; apply Z_to_bv_bv_unsigned).
(* the return state's re-aligned frame (atom 9: writable [0, 88), the slot +80) and the frame's shadow (atom 47) *)
pose proof (fsw_region_nth E _ _ 1 (YP09.mkRegion (Some 9%nat) 0 88 0 88 psj_scs0) HS eq_refl) as R9.
cbn [ms_mem restrict] in R9.
destruct R9 as (_ & _ & W9 & C9). cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in W9, C9.
rewrite E9 in W9, C9.
pose proof (fsw_region_nth E _ _ 3 (YP09.mkRegion (Some 47%nat) 0 8 0 8 ps_fsh_chunks) HS eq_refl) as R47.
cbn [ms_mem restrict] in R47.
destruct R47 as (_ & _ & W47 & C47). cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in W47, C47.
rewrite E47 in W47, C47.
assert (C47_4 : YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms)) (shadow_addr F)
                  (YP09.mkChunk 4 (CVal 1 (SLit 248)))).
{ rewrite Forall_forall in C47. apply C47. unfold ps_fsh_chunks. cbn [In].
  right; right; right; right; left; reflexivity. }
destruct psj_runT as (_ & _ & _ & _ & HPCT & HRGT & HRVT).
destruct (psj_runH lo hi Hrng) as (HRUNH & HPCH & HRGH & HMH & HRVH).
apply (psj_tok L s E ms STK sp0 FP ly S W0 mem0 md0 own lyc Sc U W mdc k Q HS HJ HARU HL E26 Hsceil HAPP HRA).
intros u1 u2 ms1 mat1 HS1 HJ1 HARU1 MEQ1.
(* ---- the cut: the byte c seated on atom 48 ---- *)
set (E2 := extK E psl_K [u1; u2]) in *.
set (E3 := ewset E2 48 (Z_to_bv 64 c)).
assert (E3_48 : ew E3 48 = Z_to_bv 64 c) by (unfold E3; apply ew_ewset_same).
assert (E3u48 : bv_unsigned (ew E3 48) = c) by (rewrite E3_48; apply wz; clear - Hc8; lia).
assert (EW : forall n, n <> 48%nat -> n <> 60%nat -> n <> 61%nat -> ew E3 n = ew E n)
  by (intros n H1 H2 H3; exact (psj_ew3 E u1 u2 _ n H1 H2 H3)).
assert (EW9 : ew E3 9 = ew E 9) by (apply EW; discriminate).
assert (EW19 : ew E3 19 = ew E 19) by (apply EW; discriminate).
assert (EW24 : ew E3 24 = ew E 24) by (apply EW; discriminate).
assert (EW26 : ew E3 26 = ew E 26) by (apply EW; discriminate).
assert (EW32 : ew E3 32 = ew E 32) by (apply EW; discriminate).
assert (EW47 : ew E3 47 = ew E 47) by (apply EW; discriminate).
assert (HS3 : st_ok tfibsegs E3 (sh_ss psj_stT) (restrict (w_H W) ms1))
  by exact (YCeo.st_ok_agree_on tfibsegs _ E2 E3 _ _ HS1 (psj_agree48 E2 _) psj_on48).
assert (HSTK : region_ok tfibsegs E3 (mrestrict (w_H W) (ms_mem ms1)) psj_stk).
{ unfold psj_stk, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite EW9, E9. split; [clear - SP9; lia|]. split; [clear - SP10; lia|]. split; [|apply Forall_nil].
  intros oo Hoo. apply (psj_writable_pt (w_H W) (ms_mem ms) (ms_mem ms1) _ (MEQ1 _)).
  apply W9. clear - Hoo; lia. }
assert (HSTR : region_ok tfibsegs E3 (mrestrict (w_H W) (ms_mem ms1)) psj_strc).
{ unfold psj_strc, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite EW26, E26. split; [clear - Hs47; lia|]. split; [clear - Hs47; lia|].
  split; [intros oo Hoo; exfalso; clear - Hoo; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val tfibsegs E3 _ s 0 1 (SOff 48 0) c);
    [rewrite fsw_SOff0, E3_48; reflexivity | clear - Hc8; cbn; lia | clear; cbn; lia|].
  intros i Hi. rewrite (psj_mbyte_pt (w_H W) (ms_mem ms) (ms_mem ms1) _ (MEQ1 _)).
  rewrite Z.add_0_r. exact (HVAL i Hi). }
assert (HDJ : all_disjoint E3 psj_strc [psj_stk]).
{ cbn [all_disjoint]. split; [|exact I]. unfold extent_disjoint, psj_strc, psj_stk.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite EW26, EW9, E26, E9. left. clear - SP1; lia. }
assert (HSC : st_ok tfibsegs E3 (psj_ssC lo hi) (restrict (w_H W) ms1)).
{ pose proof (st_ok_submem tfibsegs E3 (sh_ss psj_stT) (restrict (w_H W) ms1) [] HS3 (submem_nil _) eq_refl) as HX1.
  pose proof (st_ok_add_region' tfibsegs E3 _ (restrict (w_H W) ms1) psj_stk HX1 ltac:(vm_compute; reflexivity))
    as HX2.
  cbn [ms_mem restrict] in HX2.
  pose proof (HX2 HSTK I) as HX3.
  pose proof (st_ok_add_region' tfibsegs E3 _ (restrict (w_H W) ms1) psj_strc HX3 ltac:(vm_compute; reflexivity))
    as HX4.
  cbn [ms_mem restrict] in HX4.
  pose proof (HX4 HSTR HDJ) as HX5.
  pose proof (st_ok_facts tfibsegs E3 _ _ (mkFacts [(48%nat, mkAF lo hi 0)] [] []) HX5
    (conj (conj (psl_afact E3 48 c lo hi E3u48 Hc) I) (conj I I))) as HX6.
  unfold psj_ssC. rewrite HPCT, HRGT, HRVT in HX6. exact HX6. }
(* ---- the plain run to the loop head: the seven stores ---- *)
eapply (fsw_run_to_AJU B fsw_wr_tbl fsw_wr_tbl_ok W FUEL PSL_HEAD E3 (psj_ssC lo hi) (psj_ssH lo hi) RS_running ms1
          STK sp0 FP ly S W0 mem0 md0 own lyc Sc U _ k Q);
  [exact HSC | exact HRUNH | exact I | exact HARU1 | exact HJ1 | | ].
{ unfold psj_ssC. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; apply Z.le_refl|].
  eapply awr_ok_cons_stack_off with (n := 9%nat) (d := sp1 - sp0);
    [reflexivity | rewrite EW9, E9; ring | cbn; clear - Hwin; lia | cbn; clear - Hsp88; lia | apply awr_ok_nil]. }
intros ms2 mat2 HS2 HJ2 HARU2 HF2 HFr2 HG2.
rewrite wvb_collapse in HJ2. rewrite wvb_collapse in HARU2. rewrite wvb_collapse.
assert (MEQ2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 8 <= a < sp1 + 64) ->
                 ms_mem ms2 (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)).
{ intros a Ha Hna. rewrite <- (MEQ1 (Z_to_bv 64 a)). apply HF2. rewrite (wz a Ha).
  intros (rr & Hinr & Hrr). unfold psj_ssC in Hinr. cbn [ss_mem In] in Hinr.
  destruct Hinr as [<-|[<-|[]]]; cbn [psj_strc psj_stk YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrr.
  - clear - Hrr; lia.
  - rewrite EW9, E9 in Hrr. apply Hna. clear - Hrr; lia. }
(* ---- the head: re-seat on the machine's register file ---- *)
set (E' := Ereg (ms_regs ms2) fs_extraT).
assert (RG : forall rr, YK11.getr (ms_regs ms2) rr = sv_denot E3 (sr_get psj_regsH rr)).
{ intros rr. rewrite <- HRGH. exact (st_ok_restrict_reg tfibsegs (w_H W) E3 (psj_ssH lo hi) ms2 rr HS2). }
assert (RGv : forall rr n kk, sr_get psj_regsH rr = SOff n kk ->
                YK11.getr (ms_regs ms2) rr = sv_denot E3 (SOff n kk))
  by (intros rr n kk Hg; rewrite (RG rr), Hg; reflexivity).
assert (A18 : bv_unsigned (ew E' 18) = c)
  by exact (psj_ew_seat (ms_regs ms2) E3 18%bv 18 48 0 c eq_refl (RGv 18%bv 48%nat 0 ltac:(vm_compute; reflexivity))
              ltac:(rewrite E3u48; apply Z.add_0_r) ltac:(clear - Hc8; lia)).
assert (A21 : bv_unsigned (ew E' 21) = F + 32)
  by exact (psj_ew_seat (ms_regs ms2) E3 21%bv 21 24 32 (F + 32) eq_refl
              (RGv 21%bv 24%nat 32 ltac:(vm_compute; reflexivity))
              ltac:(rewrite EW24, E24; reflexivity) ltac:(clear - H24r; lia)).
assert (A22 : bv_unsigned (ew E' 22) = shadow_addr F)
  by exact (psj_ew_seat (ms_regs ms2) E3 22%bv 22 47 0 (shadow_addr F) eq_refl
              (RGv 22%bv 47%nat 0 ltac:(vm_compute; reflexivity))
              ltac:(rewrite EW47, E47; apply Z.add_0_r) ltac:(clear - SP4 SP5; lia)).
assert (A24 : bv_unsigned (ew E' 24) = s)
  by exact (psj_ew_seat (ms_regs ms2) E3 24%bv 24 26 0 s eq_refl (RGv 24%bv 26%nat 0 ltac:(vm_compute; reflexivity))
              ltac:(rewrite EW26, E26; apply Z.add_0_r) ltac:(clear - Hs47; lia)).
assert (A26 : bv_unsigned (ew E' 26) = s)
  by exact (psj_ew_seat (ms_regs ms2) E3 26%bv 26 26 0 s eq_refl (RGv 26%bv 26%nat 0 ltac:(vm_compute; reflexivity))
              ltac:(rewrite EW26, E26; apply Z.add_0_r) ltac:(clear - Hs47; lia)).
assert (A19 : bv_unsigned (ew E' 19) = o)
  by exact (psj_ew_seat (ms_regs ms2) E3 19%bv 19 19 0 o eq_refl (RGv 19%bv 19%nat 0 ltac:(vm_compute; reflexivity))
              ltac:(rewrite EW19, E19; apply Z.add_0_r) ltac:(rewrite <- E19; apply u64_range)).
assert (A32 : ew E' 32 = Z_to_bv 64 SHADOW_OFF)
  by (unfold E'; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (HAT : psl_at E' c s (F + 32) (shadow_addr F) o s)
  by exact (conj A18 (conj A21 (conj A22 (conj A24 (conj A26 (conj A19 A32)))))).
assert (HSH : region_ok tfibsegs E' (mrestrict (w_H W) (ms_mem ms2)) psl_sh_region).
{ unfold psl_sh_region, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite A22. split; [clear - SP4; lia|]. split; [clear - SP5; lia|]. split.
  - intros oo Hoo. apply (psj_writable_pt (w_H W) (ms_mem ms) (ms_mem ms2)).
    + apply MEQ2; clear - Hoo SP3 SP4 SP5; lia.
    + apply W47. exact Hoo.
  - (* the eight shadow bytes: +4 (0xf8, PSL_POIS here, 248 in ps_fsh_chunks), then the seven literal ones *)
    constructor.
    + apply (psj_chunk_f8 E E' (mrestrict (w_H W) (ms_mem ms)) _ (shadow_addr F) C47_4).
      apply psj_mbyte_pt. apply MEQ2; clear - SP3 SP4 SP5; lia.
    + repeat (constructor;
        [ apply (psj_chunk_lit_pt E E' (mrestrict (w_H W) (ms_mem ms)));
          [ apply (proj1 (Forall_forall _ _) C47); unfold ps_fsh_chunks; cbn [In];
            solve [repeat first [left; reflexivity | right]]
          | intros i Hi; cbn in Hi; apply psj_mbyte_pt; apply MEQ2; cbn [YP09.c_off];
            clear - Hi SP3 SP4 SP5; lia ]
        | ]).
      apply Forall_nil. }
assert (HBY : region_ok tfibsegs E' (mrestrict (w_H W) (ms_mem ms2)) psl_byte_region).
{ unfold psl_byte_region, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite A24. split; [clear - SP6; lia|]. split; [clear - SP7; lia|].
  split; [intros oo Hoo; exfalso; clear - Hoo; lia | apply Forall_nil]. }
assert (HPD : pairwise_disjoint E' [psl_sh_region; psl_byte_region]).
{ cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
  unfold extent_disjoint, psl_sh_region, psl_byte_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite A22, A24. clear - SP2; lia. }
assert (H0 : st_ok tfibsegs E' (mkSS PSL_HEAD sr_atoms [psl_sh_region; psl_byte_region] None
                                  (mkFacts (psl_atoms lo hi) [] [])) (restrict (w_H W) ms2)).
{ apply (psj_st_ok_reseat E3 E' (psj_ssH lo hi)
           (mkSS PSL_HEAD sr_atoms [psl_sh_region; psl_byte_region] None (mkFacts (psl_atoms lo hi) [] []))
           (restrict (w_H W) ms2) HS2 HRVH (eq_sym HPCH) eq_refl).
  - exact (regs_ok_Ereg (ms_regs ms2) fs_extraT).
  - split; [vm_compute; reflexivity|].
    split; [constructor; [exact HSH | constructor; [exact HBY | constructor]] | exact HPD].
  - exact (psl_facts_ok E' c s (F + 32) (shadow_addr F) o s lo hi HAT HBD). }
assert (G23 : YK11.getr (ms_regs (restrict (w_H W) ms2)) 23%bv = sv_denot E' (SOff 32 0)).
{ cbn [ms_regs restrict]. rewrite (RGv 23%bv 32%nat 0 ltac:(vm_compute; reflexivity)), !fsw_SOff0, EW32, E32, A32.
  reflexivity. }
assert (G25 : YK11.getr (ms_regs (restrict (w_H W) ms2)) 25%bv = sv_denot E' (SLit 34)).
{ cbn [ms_regs restrict]. rewrite (RG 25%bv). change (sr_get psj_regsH 25%bv) with (SLit 34).
  rewrite !psl_lit_denot. reflexivity. }
assert (G20 : YK11.getr (ms_regs (restrict (w_H W) ms2)) 20%bv = sv_denot E' (SOff 24 1)).
{ cbn [ms_regs restrict]. rewrite (RGv 20%bv 26%nat 1 ltac:(vm_compute; reflexivity)). apply psj_SOff_eq.
  unfold E'. rewrite (ew_Ereg_nat (ms_regs ms2) fs_extraT 24 24%bv eq_refl),
    (RGv 24%bv 26%nat 0 ltac:(vm_compute; reflexivity)), fsw_SOff0.
  reflexivity. }
pose proof (st_ok_set_reg tfibsegs E' _ _ 23%bv (SOff 32 0) H0 ltac:(discriminate) G23) as H1.
pose proof (st_ok_set_reg tfibsegs E' _ _ 25%bv (SLit 34) H1 ltac:(discriminate) G25) as H2.
pose proof (st_ok_set_reg tfibsegs E' _ _ 20%bv (SOff 24 1) H2 ltac:(discriminate) G20) as H3.
assert (HHEAD : st_ok tfibsegs E' (psl_head lo hi) (restrict (w_H W) ms2)) by exact H3.
(* ---- what the head env keeps of the return env, and the slots ---- *)
assert (HAGR : forall n, In n [2%nat; 3%nat; 4%nat; 8%nat; 9%nat; 27%nat] -> ew E' n = ew E n).
{ intros n Hn. cbv [In] in Hn.
  destruct Hn as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
    unfold E'; rewrite ew_Ereg_lt by (apply Nat.ltb_lt; reflexivity); rewrite RG;
    lazymatch goal with |- sv_denot _ (sr_get psj_regsH ?rr) = _ =>
      let v := eval vm_compute in (sr_get psj_regsH rr) in change (sr_get psj_regsH rr) with v end;
    rewrite fsw_SOff0; apply EW; discriminate. }
pose proof (fsw_region_nth E3 (psj_ssH lo hi) (restrict (w_H W) ms2) 1 psj_stk7 HS2
  ltac:(rewrite HMH; reflexivity)) as RH9.
cbn [ms_mem restrict] in RH9.
pose proof (YCeo.region_ok_agree_on tfibsegs psj_P E3 E _ psj_stk7 (psj_agree3 E u1 u2 _) psj_stk7_on RH9) as RE9.
assert (D24 : sv_denot E (SOff 24 0) = Z_to_bv 64 F)
  by (rewrite fsw_SOff0, <- E24; symmetry; apply Z_to_bv_bv_unsigned).
assert (HF64 : 0 <= F < 2 ^ (8 * Z.of_N 8)) by (change (8 * Z.of_N 8) with 64; clear - H24r; lia).
pose proof (fsw_field E _ 9 sp1 psj_scs7 8 64 8 64 8 8 (SOff 24 0) F RE9 E9
  ltac:(unfold psj_scs7; cbn [In]; right; right; right; right; right; left; reflexivity) D24 HF64
  ltac:(clear; cbn; lia)) as HV8.
pose proof (fsw_field E _ 9 sp1 psj_scs7 8 64 8 64 16 8 (SOff 24 0) F RE9 E9
  ltac:(unfold psj_scs7; cbn [In]; right; right; right; right; right; right; left; reflexivity) D24 HF64
  ltac:(clear; cbn; lia)) as HV16.
destruct RE9 as (_ & _ & _ & CE9). cbn [psj_stk7 YP09.r_base YP09.r_chunks base_val] in CE9. rewrite E9 in CE9.
assert (HC1 : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms2)) sp1) psj_scs1).
{ unfold psj_scs1. apply Forall_app. split; [exact CE9|].
  constructor; [|constructor].
  apply (psj_chunk_pt E (mrestrict (w_H W) (ms_mem ms))); [exact (Forall_inv C9)|].
  intros i Hi. cbn in Hi. cbn [YP09.c_off]. apply psj_mbyte_pt. apply MEQ2; clear - Hi SP9 SP10; lia. }
exact (KONT ms2 mat2 E' HHEAD HJ2 HARU2 HAT HBD HAGR MEQ2 HC1 HV8 HV16).
Qed.

End J.
