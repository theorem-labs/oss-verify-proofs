(* SCRATCH (a Theorem Labs lane): put_string's SCAN LOOP, image A (fs.asan). Folded into FSW_put_string.v. *)
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
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K
FSW_writer_tbl FSW_writer_model FSW_put_string.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSH_Fn_writer FSW_writer_kit.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the loop's shared data and helpers (the PSL and psl names) are FSW_put_string's; these four are this part's ---- *)
Lemma psl_bd_bytereg : forall c q esc shF r lo hi,
  psl_bd c q esc shF r lo hi -> q + 1 <= 2 ^ 47 - 8 -> 0 <= q + 1 /\ q + 1 + 2 <= 2 ^ 64.
Proof. unfold psl_bd. intros c q esc shF r lo hi H H1. lia. Qed.
Lemma psl_out_split : forall a b, ~ (b <= a < b + 8) -> a < b \/ b + 8 <= a.
Proof. intros a b H. lia. Qed.
Lemma psl_byte_region_ok : forall E m b,
  0 <= b -> b + 2 <= 2 ^ 64 -> bv_unsigned (ew E 24) = b ->
  region_ok tfibsegs E m psl_byte_region.
Proof.
  intros E m b H0 H1 Hb. unfold psl_byte_region, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Hb. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia | apply Forall_nil].
Qed.
Lemma psl_disj_sh : forall E shF b,
  bv_unsigned (ew E 22) = shF -> bv_unsigned (ew E 24) = b ->
  (b + 1 < shF \/ shF + 8 <= b + 1) ->
  all_disjoint E psl_sh_region [psl_byte_region].
Proof.
  intros E shF b H22 H24 Hd. apply all_disjoint_of_extents.
  unfold extent_of_region, psl_sh_region, psl_byte_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite H22, H24.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. split; [|exact I]. lia.
Qed.
(* the head's byte region at q + 1 lies off the frame's shadow granule (the byte after the loaded one) *)
Lemma psl_sep_next : forall q shF, (forall a, q + 1 <= a <= q + 2 -> ~ (shF <= a < shF + 8)) ->
  q + 1 + 1 < shF \/ shF + 8 <= q + 1 + 1.
Proof. intros q shF H. pose proof (H (q + 2) ltac:(lia)) as H2. lia. Qed.
Lemma psl_d64 : forall d, 1 <= d <= 255 -> 0 <= d < 2 ^ 64.
Proof. intros d H. lia. Qed.
Lemma psl_z0 : 0 <= 0 < 2 ^ 64.
Proof. lia. Qed.
Lemma psl_nat_lt1 : forall i, ~ (S i < 1)%nat.
Proof. intros i H. lia. Qed.
(* psl_at survives an env that changes only the four scratch atoms 10 / 11 / 12 / 18, with 18 re-read *)
Lemma psl_at_scr : forall E E' c c' q esc shF o r,
  psl_at E c q esc shF o r ->
  (forall n, n <> 10%nat -> n <> 11%nat -> n <> 12%nat -> n <> 18%nat -> ew E' n = ew E n) ->
  bv_unsigned (ew E' 18) = c' -> psl_at E' c' q esc shF o r.
Proof.
  intros E E' c c' q esc shF o r (_ & H21 & H22 & H24 & H26 & H19 & H32) HO H18. unfold psl_at.
  rewrite (HO 21%nat), (HO 22%nat), (HO 24%nat), (HO 26%nat), (HO 19%nat), (HO 32%nat) by discriminate.
  repeat split; assumption.
Qed.

(* ================= the last iteration: the byte at q + 1 is the terminating zero ================= *)
(* L: from the data-load cut with the loaded byte 0 to PSL_END. MEASURED: the engine does not decide the EQ test
   from the singleton range (33, [0, 0]) (it stops at 0x85d4c `SR_branch BC_NE (SOff 33 0) (SLit 0)`), so the walk
   seats the condition. At PSL_END x24 = SOff 24 1 (the zero's address) and x20 = SOff 24 2, the same register file
   psl_ssD has at the head, so the loop's shift lands on psl_regsF here too. *)
Definition psl_ssCL (lo hi : Z) : sstate := add_cond (psl_ssC lo hi 0 0) (mkAC BC_EQ (SOff 33 0) (SLit 0)).
Definition psl_ssL (lo hi : Z) : sstate := fst (sym_run_toN tfibsegs fsw_wr_tbl FUEL PSL_END (psl_ssCL lo hi)).
Lemma psl_runL : forall lo hi, psl_rng lo hi ->
  sym_run_toN tfibsegs fsw_wr_tbl FUEL PSL_END (psl_ssCL lo hi) = (psl_ssL lo hi, RS_running)
  /\ ss_mem (psl_ssL lo hi) = [psl_byte_region_c]
  /\ ss_resv (psl_ssL lo hi) = None.
Proof.
  intros lo hi [(-> & ->) | [(-> & ->) | (-> & ->)]];
    (split; [vm_compute; reflexivity|]); (split; vm_compute; reflexivity).
Qed.
Lemma psl_runLF : forall lo hi, psl_rng lo hi ->
  ss_rebase psl_rb (mkSS (ss_pc (psl_ssL lo hi)) (ss_regs (psl_ssL lo hi))
                         (ss_mem (psl_ssL lo hi)) (ss_resv (psl_ssL lo hi)) psl_G) psl_G
  = mkSS PSL_END psl_regsF [psl_byte_regionF] None psl_G.
Proof. intros lo hi [(-> & ->) | [(-> & ->) | (-> & ->)]]; vm_compute; reflexivity. Qed.

(* the state at PSL_END the loop hands on: the head's register file (atom 24 = the zero's address), the frame's
   shadow granule with its 0xf8 byte back, the shift's facts *)
Definition psl_end_ss : sstate := mkSS PSL_END psl_regs [psl_sh_region] None psl_G.
Definition psl_at_end (E : env) (qe esc shF o r : Z) : Prop := psl_at E 0 qe esc shF o r.

(* ---- small arithmetic for the scan's induction (kept out of the walk's context) ---- *)
Lemma psl_d1 : forall d, plain_byte d -> 0 <= d < 256 -> 1 <= d <= 255.
Proof. intros d (H32 & _ & _) H. lia. Qed.
Lemma psl_sepB : forall q shF, ~ (shF <= q + 1 < shF + 8) -> ~ (shF <= q + 1 + 1 < shF + 8) ->
  forall a, q + 1 <= a <= q + 2 -> ~ (shF <= a < shF + 8).
Proof. intros q shF H1 H2 a Ha. lia. Qed.
Lemma psl_q_step : forall q n, q + 1 + Z.of_nat (S n) <= 2 ^ 47 - 8 ->
  q + 1 <= 2 ^ 47 - 8 /\ q + 1 + 1 + Z.of_nat n <= 2 ^ 47 - 8.
Proof. intros q n H. lia. Qed.
Lemma psl_addr_succ : forall q i, q + 1 + 1 + Z.of_nat i = q + 1 + Z.of_nat (S i).
Proof. intros q i. lia. Qed.
Lemma psl_cell_rng : forall c q esc shF r lo hi i n,
  psl_bd c q esc shF r lo hi -> (i <= n)%nat -> q + 1 + 1 + Z.of_nat n <= 2 ^ 47 - 8 ->
  0 <= q + 1 + 1 + Z.of_nat i <= 2 ^ 47.
Proof. unfold psl_bd. intros c q esc shF r lo hi i n H Hi Hn. lia. Qed.
(* the atoms a later stretch reads that the loop never moves: sp / gp / tp / s0 / sp1 / s11 (2 3 4 8 9 27). The walk
   changes only the token atoms 60 / 61, the loaded byte 33, the pointer 24 and the scratch atoms 10 / 11 / 12 / 18. *)
Lemma psl_keep6 : forall E E2 E3 E4 E5 : env,
  (forall n, (n < 60)%nat -> ew E2 n = ew E n) ->
  (forall n, n <> 33%nat -> ew E3 n = ew E2 n) ->
  (forall n, n <> 24%nat -> ew E4 n = ew E3 n) ->
  (forall n, n <> 10%nat -> n <> 11%nat -> n <> 12%nat -> n <> 18%nat -> ew E5 n = ew E4 n) ->
  forall n, In n [2%nat; 3%nat; 4%nat; 8%nat; 9%nat; 27%nat] -> ew E5 n = ew E n.
Proof.
  intros E E2 E3 E4 E5 H2 H3 H4 H5 n Hn. cbn [In] in Hn.
  repeat destruct Hn as [<-|Hn]; try destruct Hn;
    rewrite H5, H4, H3, H2 by (discriminate || lia); reflexivity.
Qed.
(* the memory of a rebuilt state, by rewriting: `cbn [ss_mem]` there leaves the kernel to compare `ss_mem D` with
   the rebuilt record's field, and with D a symbolic-run constant (psl_ssD, psl_ssL) the kernel then evaluates the run
   (MEASURED: psl_iter's Qed timed out on exactly that step; with this rewrite it does not reduce D at all) *)
Lemma psl_mem_mk : forall pc rs m rv G, ss_mem (mkSS pc rs m rv G) = m.
Proof. reflexivity. Qed.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

(* ---- the four scratch registers x10 / x11 / x12 / x18 re-seated on the head's own atoms ---- *)
Definition psl_seat (E : env) (ms : machine_state) : env :=
  ewset (ewset (ewset (ewset E 10 (YK11.getr (ms_regs ms) 10%bv)) 11 (YK11.getr (ms_regs ms) 11%bv))
          12 (YK11.getr (ms_regs ms) 12%bv)) 18 (YK11.getr (ms_regs ms) 18%bv).
Lemma psl_seat_other : forall E ms n, n <> 10%nat -> n <> 11%nat -> n <> 12%nat -> n <> 18%nat ->
  ew (psl_seat E ms) n = ew E n.
Proof.
  intros E ms n H10 H11 H12 H18. unfold psl_seat.
  rewrite (ew_ewset_other _ 18%nat _ n H18), (ew_ewset_other _ 12%nat _ n H12),
          (ew_ewset_other _ 11%nat _ n H11), (ew_ewset_other _ 10%nat _ n H10).
  reflexivity.
Qed.
Lemma psl_seat_ed : forall E ms, ed (psl_seat E ms) = ed E.
Proof. intros E ms. unfold psl_seat. rewrite !ed_ewset. reflexivity. Qed.
Lemma psl_seat_10 : forall E ms, ew (psl_seat E ms) 10 = YK11.getr (ms_regs ms) 10%bv.
Proof.
  intros E ms. unfold psl_seat.
  rewrite (ew_ewset_other _ 18%nat _ 10%nat ltac:(discriminate)),
          (ew_ewset_other _ 12%nat _ 10%nat ltac:(discriminate)),
          (ew_ewset_other _ 11%nat _ 10%nat ltac:(discriminate)).
  apply ew_ewset_same.
Qed.
Lemma psl_seat_11 : forall E ms, ew (psl_seat E ms) 11 = YK11.getr (ms_regs ms) 11%bv.
Proof.
  intros E ms. unfold psl_seat.
  rewrite (ew_ewset_other _ 18%nat _ 11%nat ltac:(discriminate)),
          (ew_ewset_other _ 12%nat _ 11%nat ltac:(discriminate)).
  apply ew_ewset_same.
Qed.
Lemma psl_seat_12 : forall E ms, ew (psl_seat E ms) 12 = YK11.getr (ms_regs ms) 12%bv.
Proof.
  intros E ms. unfold psl_seat. rewrite (ew_ewset_other _ 18%nat _ 12%nat ltac:(discriminate)).
  apply ew_ewset_same.
Qed.
Lemma psl_seat_18 : forall E ms, ew (psl_seat E ms) 18 = YK11.getr (ms_regs ms) 18%bv.
Proof. intros E ms. unfold psl_seat. apply ew_ewset_same. Qed.
(* after the shift (psl_regsF: x10 / x11 / x12 / x18 = atoms 24 / 60 / 61 / 33) the walk re-seats the four on
   atoms 10 / 11 / 12 / 18 and gets the head's register file psl_regs back; atom 18 then holds the loaded byte *)
Lemma psl_reseat : forall pc E ms,
  st_ok tfibsegs E (mkSS pc psl_regsF [] None psl_G) ms ->
  exists E', st_ok tfibsegs E' (mkSS pc psl_regs [] None psl_G) ms /\ ew E' 18 = ew E 33 /\
    (forall n, n <> 10%nat -> n <> 11%nat -> n <> 12%nat -> n <> 18%nat -> ew E' n = ew E n).
Proof.
  intros pc E ms HS.
  assert (R18 : sr_get psl_regsF 18%bv = SOff 33 0) by (vm_compute; reflexivity).
  assert (H18 : YK11.getr (ms_regs ms) 18%bv = ew E 33).
  { rewrite (st_ok_reg tfibsegs E _ ms 18%bv HS). cbn [ss_regs]. rewrite R18. apply fsw_SOff0. }
  exists (psl_seat E ms). split; [|split; [rewrite psl_seat_18; exact H18 | apply psl_seat_other]].
  assert (HAG : YCeo.env_agree_on
    (fun n => negb (orb (orb (Nat.eqb n 10) (Nat.eqb n 11)) (orb (Nat.eqb n 12) (Nat.eqb n 18))))
    E (psl_seat E ms)).
  { split; [|apply psl_seat_ed]. intros n Hn.
    apply psl_seat_other; intros ->; cbn in Hn; discriminate Hn. }
  pose proof (YCeo.st_ok_agree_on tfibsegs _ E (psl_seat E ms) _ ms HS HAG
    ltac:(vm_compute; reflexivity)) as HS1.
  pose proof (st_ok_set_reg tfibsegs _ _ ms 10%bv (SOff 10 0) HS1 ltac:(discriminate)
    ltac:(rewrite fsw_SOff0, psl_seat_10; reflexivity)) as HS2.
  pose proof (st_ok_set_reg tfibsegs _ _ ms 11%bv (SOff 11 0) HS2 ltac:(discriminate)
    ltac:(rewrite fsw_SOff0, psl_seat_11; reflexivity)) as HS3.
  pose proof (st_ok_set_reg tfibsegs _ _ ms 12%bv (SOff 12 0) HS3 ltac:(discriminate)
    ltac:(rewrite fsw_SOff0, psl_seat_12; reflexivity)) as HS4.
  pose proof (st_ok_set_reg tfibsegs _ _ ms 18%bv (SOff 18 0) HS4 ltac:(discriminate)
    ltac:(rewrite fsw_SOff0, psl_seat_18; reflexivity)) as HS5.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS5. rewrite psl_regsF_set in HS5. exact HS5.
Qed.

(* one byte of the string as psl_iter / psl_last read it: its shadow says addressable, it holds v, and neither the
   byte nor its shadow byte lies in the frame's shadow granule; the byte is no shadow byte *)
Definition psl_cell (W : world tfibsegs) (m : word -> option byte) (shF a v : Z) : Prop :=
  range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF a 1 /\
  val_mem tfibsegs (mrestrict (w_H W) m) a 1 v /\
  ~ (shF <= a < shF + 8) /\ ~ (shF <= SHADOW_OFF + a / 8 < shF + 8) /\
  ~ (SHADOW_OFF <= a < SHADOW_OFF + 17592186044416).
(* a cell is kept by any memory that agrees off the frame's shadow granule *)
Lemma psl_cell_eq : forall (W : world tfibsegs) (m m' : word -> option byte) shF a v,
  0 <= a <= 2 ^ 47 ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (shF <= x < shF + 8) -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
  psl_cell W m shF a v -> psl_cell W m' shF a v.
Proof.
  intros W m m' shF a v Ha HM (HRA & HV & HB & HS & HP).
  assert (HMr : forall x, 0 <= x < 2 ^ 64 -> ~ (shF <= x < shF + 8) ->
    mbyte tfibsegs (mrestrict (w_H W) m') x = mbyte tfibsegs (mrestrict (w_H W) m) x)
    by (intros x Hx Hnx; unfold mbyte, mrestrict; rewrite (HM x Hx Hnx); reflexivity).
  split; [|split; [|exact (conj HB (conj HS HP))]].
  - eapply range_addressable_agree; [|exact HRA]. intros x Hx.
    unfold aview, shadow_of_addr. replace x with a by lia.
    rewrite (HMr (SHADOW_OFF + a / 8)); [reflexivity| |exact HS].
    unfold SHADOW_OFF. pose proof (Z.div_le_mono 0 a 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound a 8 (2 ^ 47) ltac:(lia) ltac:(lia)). lia.
  - intros i Hi. destruct i as [|i]; [|exfalso; exact (psl_nat_lt1 i Hi)].
    rewrite (HMr (a + Z.of_nat 0)); [exact (HV 0%nat Hi) | cbn [Z.of_nat]; lia |].
    cbn [Z.of_nat]. rewrite Z.add_0_r. exact HB.
Qed.

(* ================= 2. ONE iteration of the scan loop ================= *)
Lemma psl_iter : forall lo hi lo' hi' (E : env) ms STK sp0 FP ly S W0 mem0 md0 own lyc Sc U
    (W : world tfibsegs) mdc k pos q shF c esc o r d (Q : world tfibsegs -> config -> Prop),
  psl_rng lo hi -> psl_rng lo' hi' ->
  st_ok tfibsegs E (psl_head lo hi) (restrict (w_H W) ms) ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison U (ms_mem ms)) mdc k ->
  ARU tfibsegs B lyc Sc U W (ms_mem ms) mdc ->
  In (0, pos) (frames Sc) -> shF = shadow_addr (frame_addr lyc 0 pos) ->
  psl_at E c q esc shF o r -> psl_bd c q esc shF r lo hi ->
  (forall a, shF <= a < shF + 8 ->
     awr_byte tfibsegs B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (frames S) a) ->
  range_addressable (aview tfibsegs (w_H W) (ms_mem ms)) SHADOW_OFF (q + 1) 1 ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (q + 1) 1 d ->
  1 <= d <= 255 -> lo' <= d <= hi' -> q + 1 <= 2 ^ 47 - 8 ->
  (forall a, q + 1 <= a <= q + 2 -> ~ (shF <= a < shF + 8)) ->
  ~ (shF <= SHADOW_OFF + (q + 1) / 8 < shF + 8) ->
  ~ (SHADOW_OFF <= q + 1 < SHADOW_OFF + 17592186044416) ->
  (forall ms' mat' E',
     st_ok tfibsegs E' (psl_head lo' hi') (restrict (w_H W) ms') ->
     ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison U (ms_mem ms'))
       (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
     ARU tfibsegs B lyc Sc U W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) ->
     psl_at E' d (q + 1) esc shF o r ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (shF <= a < shF + 8) ->
        ms_mem ms' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) ->
     (forall n, In n [2%nat; 3%nat; 4%nat; 8%nat; 9%nat; 27%nat] -> ew E' n = ew E n) ->
     SRr tfibsegs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros lo hi lo' hi' E ms STK sp0 FP ly S W0 mem0 md0 own lyc Sc U W mdc k pos q shF c esc o r d Q
  HrngA HrngB HS HJ HARU Hin HshF HAT HBD HAWRsh HRA HVAL Hd Hd' Hq1 HSEPB HSEPS HAPP KONT.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HAT as (E18 & E21 & E22 & E24 & E26 & E19 & E32).
pose proof HBD as (Bc & Be & Bs & Bq & Br).
destruct (psl_runA lo hi HrngA) as (HRUNA & HMA & HFA & HVA).
destruct (psl_runB lo hi HrngA) as (HSTAT & HRUNB & HOBL & HJJ & HPCB & HMB & HFB & HVB).
destruct (psl_runD lo hi HrngA) as (HRUND & HPCD & HMD & HVD).
(* ---- phase A: the head to the inline shadow check ---- *)
eapply (fsw_run_to_AJU B fsw_wr_tbl fsw_wr_tbl_ok W FUEL PSL_SHCHK E (psl_head lo hi) (psl_ssA lo hi)
          RS_running ms STK sp0 FP ly S W0 mem0 md0 own lyc Sc U mdc k Q);
  [exact HS | exact HRUNA | exact I | exact HARU | exact HJ | | ].
{ cbn [ss_mem psl_head].
  eapply awr_ok_cons_gen with (k := 22%nat) (b := shF);
    [reflexivity | exact E22 | cbn [psl_sh_region YP09.r_wlo YP09.r_whi]; intros a Ha; apply HAWRsh; lia |].
  apply awr_ok_cons_ro; [cbn [psl_byte_region YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]. }
intros ms1 mat1 HS1 HJ1 HARU1 HF1 HFr1 HG1.
cbn [ms_mem mkst] in HF1, HFr1, HG1, HJ1, HARU1.
assert (MEQ1 : forall a, 0 <= a < 2 ^ 64 -> ~ (shF <= a < shF + 8) ->
  ms_mem ms1 (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)).
{ intros a Ha Hna. apply HF1. rewrite (wz a Ha). intros (rr & Hinr & Hrr).
  cbn [ss_mem psl_head In] in Hinr. destruct Hinr as [<-|[<-|[]]];
    cbn [psl_sh_region psl_byte_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrr;
    rewrite ?E22 in Hrr; lia. }
assert (MEQ1r : forall a, 0 <= a < 2 ^ 64 -> ~ (shF <= a < shF + 8) ->
  mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms1)) a = mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms)) a)
  by (intros a Ha Hna; unfold mbyte, mrestrict; rewrite (MEQ1 a Ha Hna); reflexivity).
assert (HRA1 : range_addressable (aview tfibsegs (w_H W) (ms_mem ms1)) SHADOW_OFF (q + 1) 1).
{ eapply range_addressable_agree; [|exact HRA]. intros x Hx.
  unfold aview, shadow_of_addr. replace x with (q + 1) by lia.
  rewrite (MEQ1r (SHADOW_OFF + (q + 1) / 8) ltac:(unfold SHADOW_OFF in *;
    pose proof (Z.div_le_mono 0 (q + 1) 8 ltac:(lia));
    pose proof (Z.div_le_upper_bound (q + 1) 8 (2 ^ 47) ltac:(lia) ltac:(lia)); lia) HSEPS).
  reflexivity. }
assert (HVAL1 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (q + 1) 1 d).
{ intros i Hi. rewrite (MEQ1r (q + 1 + Z.of_nat i) ltac:(cbn in Hi; lia)
    ltac:(apply HSEPB; cbn in Hi; lia)). exact (HVAL i Hi). }
(* ---- phase B: the token run over the inline check, without the shadow region ---- *)
assert (HSB : st_ok tfibsegs E (psl_ssB lo hi) (restrict (w_H W) ms1)).
{ pose proof (st_ok_submem tfibsegs E (psl_ssA lo hi) (restrict (w_H W) ms1) [psl_byte_region] HS1
    ltac:(rewrite HMA; apply submem_drop; apply submem_keep;
          [apply subregion_refl | apply submem_nil])
    ltac:(vm_compute; reflexivity)) as HX.
  unfold psl_ssB. rewrite <- HVA. exact HX. }
assert (E24' : ew E 24 = Z_to_bv 64 q)
  by (rewrite <- E24; symmetry; apply Z_to_bv_bv_unsigned).
assert (SHOK : sh_ok tfibsegs fs_Bx psl_SH E (mrestrict (w_H W) (ms_mem ms1))).
{ unfold psl_SH. constructor; [|constructor].
  apply (shent_ok_of_range tfibsegs (w_H W) (ms_mem ms1) E fs_Bx 24%nat (q + 1) 1 q 1 2 HRA1).
  - unfold fs_Bx. apply (U_atom E 32 SHADOW_OFF E32). unfold SHADOW_OFF; lia.
  - apply (U_atom E 24 q E24'). lia.
  - lia.
  - lia.
  - intros x Hx. cbn [Z.min Z.max] in Hx.
    assert (Hxq : x = q + 1) by lia. rewrite Hxq. exact HAPP. }
eapply (fsw_run_tok_AJU B fsw_wr_tbl fsw_wr_tbl_ok W FUEL E psl_K fs_Bx fs_Bspan psl_SH
          (psl_ssB lo hi) (psl_stB lo hi) (TS_stopped (SR_load (Some 24%nat) 1)) ms1
          STK sp0 FP ly S W0 mem0 md0 own lyc Sc U _ k Q);
  [exact HSB | exact SHOK | exact HSTAT | exact HRUNB | exact I | exact HARU1 | exact HJ1
  | rewrite HOBL; apply Forall_nil | | ].
{ cbn [psl_ssB ss_mem].
  apply awr_ok_cons_ro; [cbn [psl_byte_region YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]. }
intros ws ms2 mat2 Hlen HS2 Hsh2 HJ2 HARU2 HF2 HFr2 HG2.
cbn [ms_mem mkst] in HF2, HFr2, HG2, HJ2, HARU2.
rewrite HJJ in Hlen.
destruct ws as [|u1 ws]; [discriminate Hlen|].
destruct ws as [|u2 ws]; [discriminate Hlen|].
destruct ws as [|u3 ws]; [|discriminate Hlen]. clear Hlen.
(* the token run writes nothing: its one region is read-only *)
assert (MEQ2 : forall x, ms_mem ms2 x = ms_mem ms1 x).
{ apply (psl_frame_ro E [psl_byte_region] (ms_mem ms1) (ms_mem ms2));
    [constructor; [cbn [psl_byte_region YP09.r_wlo YP09.r_whi]; lia | constructor]|].
  unfold psl_ssB in HF2; cbn [ss_mem] in HF2; exact HF2. }
set (E2 := extK E psl_K [u1; u2]) in *.
assert (EW2 : forall n, (n < 60)%nat -> ew E2 n = ew E n).
{ intros n Hn. unfold E2, psl_K. cbn [extK].
  rewrite (ew_ewset_other (ewset E 60 u1) 61 u2 n ltac:(lia)), (ew_ewset_other E 60 u1 n ltac:(lia)).
  reflexivity. }
assert (HAT2 : psl_at E2 c q esc shF o r).
{ unfold psl_at.
  rewrite (EW2 18%nat ltac:(lia)), (EW2 21%nat ltac:(lia)), (EW2 22%nat ltac:(lia)),
          (EW2 24%nat ltac:(lia)), (EW2 26%nat ltac:(lia)), (EW2 19%nat ltac:(lia)),
          (EW2 32%nat ltac:(lia)).
  exact HAT. }
(* ---- the cut at the data load: the byte's value comes from the spec, as a fresh atom 33 ---- *)
set (E3 := ewset E2 33 (Z_to_bv 64 d)) in *.
assert (EW3 : forall n, n <> 33%nat -> ew E3 n = ew E2 n)
  by (intros n Hn; unfold E3; apply ew_ewset_other; exact Hn).
assert (E3_33 : ew E3 33 = Z_to_bv 64 d) by (unfold E3; apply ew_ewset_same).
assert (HAG3 : YCeo.env_agree_on (fun n => negb (Nat.eqb n 33)) E2 E3).
{ split; [|unfold E3; apply ed_ewset].
  intros n Hn. apply EW3. intros ->. cbn in Hn. discriminate Hn. }
assert (HS3 : st_ok tfibsegs E3 (sh_ss (psl_stB lo hi)) (restrict (w_H W) ms2))
  by exact (YCeo.st_ok_agree_on tfibsegs _ E2 E3 _ _ HS2 HAG3 (psl_on33 lo hi HrngA)).
(* the byte at q + 1 is what cstr_ok says, on the memory the run reached *)
assert (HVAL2 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms2)) (q + 1) 1 d).
{ intros i Hi. unfold mbyte, mrestrict. rewrite (MEQ2 (Z_to_bv 64 (q + 1 + Z.of_nat i))).
  exact (HVAL1 i Hi). }
assert (HSC : st_ok tfibsegs E3 (psl_ssC lo hi 1 255) (restrict (w_H W) ms2)).
{ pose proof (st_ok_submem tfibsegs E3 (sh_ss (psl_stB lo hi)) (restrict (w_H W) ms2) [] HS3
    (submem_nil _) ltac:(reflexivity)) as HX1.
  pose proof (st_ok_add_region' tfibsegs E3 _ (restrict (w_H W) ms2) psl_byte_region_c HX1
    ltac:(vm_compute; reflexivity)) as HX2.
  cbn [ms_mem restrict] in HX2.
  assert (HROK : region_ok tfibsegs E3 (mrestrict (w_H W) (ms_mem ms2)) psl_byte_region_c).
  { unfold psl_byte_region_c, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite (EW3 24%nat ltac:(discriminate)), (EW2 24%nat ltac:(lia)), E24.
    split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs E3 _ q 1 1 (SOff 33 0) d);
      [rewrite fsw_SOff0, E3_33; reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
      | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; exact HVAL2]. }
  pose proof (HX2 HROK I) as HX3.
  pose proof (st_ok_add_fact tfibsegs E3 _ (restrict (w_H W) ms2) 33%nat (mkAF 1 255 0) HX3
    (psl_afact E3 33%nat d 1 255 ltac:(rewrite E3_33; apply wz; lia) Hd)) as HX4.
  unfold psl_ssC. rewrite HPCB, HFB, HVB in HX4. exact HX4. }
(* ---- phase D: from the cut back to the loop head ---- *)
eapply (fsw_run_to_AJU B fsw_wr_tbl fsw_wr_tbl_ok W FUEL PSL_HEAD E3 (psl_ssC lo hi 1 255)
          (psl_ssD lo hi 1 255) RS_running ms2 STK sp0 FP ly S W0 mem0 md0 own lyc Sc U _ k Q);
  [exact HSC | exact HRUND | exact I | exact HARU2 | exact HJ2 | | ].
{ unfold psl_ssC, add_atom. cbn [ss_mem].
  apply awr_ok_cons_ro; [cbn [psl_byte_region_c YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]. }
intros ms3 mat3 HS4 HJ4 HARU4 HF4 HFr4 HG4.
cbn [ms_mem mkst] in HF4, HFr4, HG4, HJ4, HARU4.
assert (MEQ3 : forall x, ms_mem ms3 x = ms_mem ms2 x).
{ apply (psl_frame_ro E3 (ss_mem (psl_ssC lo hi 1 255)) (ms_mem ms2) (ms_mem ms3));
    [unfold psl_ssC, add_atom; cbn [ss_mem];
     constructor; [cbn [psl_byte_region_c YP09.r_wlo YP09.r_whi]; lia | constructor]
    | exact HF4]. }
assert (MEQ31 : forall x, ms_mem ms3 x = ms_mem ms1 x)
  by (intros x; rewrite MEQ3; apply MEQ2).
(* ---- the loop's shift: the next head's pointer is q + 1 ---- *)
assert (HAT3 : psl_at E3 c q esc shF o r).
{ unfold psl_at.
  rewrite (EW3 18%nat ltac:(discriminate)), (EW3 21%nat ltac:(discriminate)),
          (EW3 22%nat ltac:(discriminate)), (EW3 24%nat ltac:(discriminate)),
          (EW3 26%nat ltac:(discriminate)), (EW3 19%nat ltac:(discriminate)),
          (EW3 32%nat ltac:(discriminate)).
  exact HAT2. }
assert (HSG : st_ok tfibsegs E3 (mkSS (ss_pc (psl_ssD lo hi 1 255)) (ss_regs (psl_ssD lo hi 1 255))
                 (ss_mem (psl_ssD lo hi 1 255)) (ss_resv (psl_ssD lo hi 1 255)) psl_G)
                 (restrict (w_H W) ms3))
  by exact (st_ok_facts tfibsegs E3 _ _ psl_G HS4 (psl_G_ok E3 c q esc shF o r lo hi HAT3 HBD)).
set (E4 := ewset E3 24 (Z_to_bv 64 (q + 1))) in *.
assert (Hq0 : 0 <= q + 1 < 2 ^ 64) by exact (psl_bd_q64 c q esc shF r lo hi HBD).
assert (E4_24 : bv_unsigned (ew E4 24) = q + 1)
  by (unfold E4; rewrite ew_ewset_same; apply wz; exact Hq0).
assert (EW4 : forall n, n <> 24%nat -> ew E4 n = ew E3 n)
  by (intros n Hn; unfold E4; apply ew_ewset_other; exact Hn).
assert (HAT4 : psl_at E4 c (q + 1) esc shF o r).
{ pose proof HAT3 as (A18 & A21 & A22 & A24 & A26 & A19 & A32). unfold psl_at.
  rewrite (EW4 18%nat ltac:(discriminate)), (EW4 21%nat ltac:(discriminate)),
          (EW4 22%nat ltac:(discriminate)), (EW4 26%nat ltac:(discriminate)),
          (EW4 19%nat ltac:(discriminate)), (EW4 32%nat ltac:(discriminate)), E4_24.
  repeat split; assumption. }
assert (HBD4 : psl_bd c (q + 1) esc shF r lo hi)
  by exact (psl_bd_shift c q esc shF r lo hi c lo hi HBD Hq1 (proj1 HBD)).
assert (HSF : st_ok tfibsegs E4 psl_ssF' (restrict (w_H W) ms3)).
{ rewrite <- (psl_runF lo hi HrngA).
  eapply (st_ok_rebase tfibsegs E3 E4 psl_rb _ _ psl_G HSG).
  - exact (psl_rebase_ok E3 E4 q (proj1 (proj2 (proj2 (proj2 HAT3)))) E4_24 EW4
             ltac:(unfold E4; apply ed_ewset)).
  - intros rr n Hinr Hb. rewrite psl_mem_mk, HMD in Hinr. cbn [In] in Hinr.
    destruct Hinr as [<-|[]]. cbn [psl_byte_region_c YP09.r_base] in Hb. injection Hb as <-.
    unfold rebase_exact, psl_rb. cbn [rb_lookup Nat.eqb].
    pose proof HAT3 as (_ & _ & _ & A24 & _). rewrite A24, E4_24. ring.
  - exact (psl_G_ok E4 c (q + 1) esc shF o r lo hi HAT4 HBD4). }
(* ---- drop the rebased byte region; re-seat x10 / x11 / x12 / x18 on the head's own atoms ---- *)
pose proof (st_ok_submem tfibsegs E4 psl_ssF' (restrict (w_H W) ms3) [] HSF (submem_nil _)
  ltac:(reflexivity)) as HSG0.
destruct (psl_reseat PSL_HEAD E4 (restrict (w_H W) ms3) HSG0) as (E5 & HS5 & E5_18 & EW5).
assert (E5_18' : bv_unsigned (ew E5 18) = d)
  by (rewrite E5_18, (EW4 33%nat ltac:(discriminate)), E3_33; exact (wz d (psl_d64 d Hd))).
pose proof (psl_at_scr E4 E5 c d (q + 1) esc shF o r HAT4 EW5 E5_18') as HAT5.
pose proof HAT5 as (_ & _ & A22 & A24 & _).
(* ---- re-add the head's two regions: the byte at q + 2, then the frame's shadow granule ---- *)
pose proof (psl_bd_bytereg c q esc shF r lo hi HBD Hq1) as (Hb0 & Hb1).
pose proof (st_ok_add_region' tfibsegs E5 _ (restrict (w_H W) ms3) psl_byte_region HS5
  ltac:(vm_compute; reflexivity) (psl_byte_region_ok E5 _ (q + 1) Hb0 Hb1 A24) I) as HS6.
assert (HROKs : region_ok tfibsegs E5 (ms_mem (restrict (w_H W) ms3)) psl_sh_region).
{ apply (psl_sh_env E E5); [rewrite A22, E22; reflexivity|].
  apply (psl_region_ok_eq E (ms_mem (restrict (w_H W) ms1)));
    [|exact (fsw_region_nth E (psl_ssA lo hi) (restrict (w_H W) ms1) 0%nat psl_sh_region HS1
             ltac:(rewrite HMA; reflexivity))].
  intros x. cbn [ms_mem restrict]. unfold mrestrict. rewrite (MEQ31 x). reflexivity. }
pose proof (st_ok_add_region' tfibsegs E5 _ (restrict (w_H W) ms3) psl_sh_region HS6
  ltac:(vm_compute; reflexivity) HROKs (psl_disj_sh E5 shF (q + 1) A22 A24 (psl_sep_next q shF HSEPB)))
  as HS7.
(* ---- the next byte's facts, and on to the continuation ---- *)
pose proof (st_ok_facts tfibsegs E5 _ _ (mkFacts (psl_atoms lo' hi') [] []) HS7
  (psl_facts_ok E5 d (q + 1) esc shF o r lo' hi' HAT5
     (psl_bd_shift c q esc shF r lo hi d lo' hi' HBD Hq1 Hd'))) as HS8.
repeat rewrite wvb_collapse in HJ4. repeat rewrite wvb_collapse in HARU4. repeat rewrite wvb_collapse.
apply (KONT ms3 mat3 E5); [exact HS8 | exact HJ4 | exact HARU4 | exact HAT5 |
  | exact (psl_keep6 E E2 E3 E4 E5 EW2 EW3 EW4 EW5)].
intros a Ha Hna. rewrite (MEQ31 (Z_to_bv 64 a)). exact (MEQ1 a Ha Hna).
Qed.

(* ================= 3. the LAST iteration: the byte at q + 1 is the terminating zero ================= *)
Lemma psl_last : forall lo hi (E : env) ms STK sp0 FP ly S W0 mem0 md0 own lyc Sc U
    (W : world tfibsegs) mdc k pos q shF c esc o r (Q : world tfibsegs -> config -> Prop),
  psl_rng lo hi ->
  st_ok tfibsegs E (psl_head lo hi) (restrict (w_H W) ms) ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison U (ms_mem ms)) mdc k ->
  ARU tfibsegs B lyc Sc U W (ms_mem ms) mdc ->
  In (0, pos) (frames Sc) -> shF = shadow_addr (frame_addr lyc 0 pos) ->
  psl_at E c q esc shF o r -> psl_bd c q esc shF r lo hi ->
  (forall a, shF <= a < shF + 8 ->
     awr_byte tfibsegs B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (frames S) a) ->
  range_addressable (aview tfibsegs (w_H W) (ms_mem ms)) SHADOW_OFF (q + 1) 1 ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (q + 1) 1 0 ->
  q + 1 <= 2 ^ 47 - 8 ->
  ~ (shF <= q + 1 < shF + 8) ->
  ~ (shF <= SHADOW_OFF + (q + 1) / 8 < shF + 8) ->
  ~ (SHADOW_OFF <= q + 1 < SHADOW_OFF + 17592186044416) ->
  (forall ms' mat' E',
     st_ok tfibsegs E' psl_end_ss (restrict (w_H W) ms') ->
     ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison U (ms_mem ms'))
       (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
     ARU tfibsegs B lyc Sc U W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) ->
     psl_at_end E' (q + 1) esc shF o r ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (shF <= a < shF + 8) ->
        ms_mem ms' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) ->
     (forall n, In n [2%nat; 3%nat; 4%nat; 8%nat; 9%nat; 27%nat] -> ew E' n = ew E n) ->
     SRr tfibsegs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros lo hi E ms STK sp0 FP ly S W0 mem0 md0 own lyc Sc U W mdc k pos q shF c esc o r Q
  HrngA HS HJ HARU Hin HshF HAT HBD HAWRsh HRA HVAL Hq1 HSEPB HSEPS HAPP KONT.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HAT as (E18 & E21 & E22 & E24 & E26 & E19 & E32).
pose proof HBD as (Bc & Be & Bs & Bq & Br).
destruct (psl_runA lo hi HrngA) as (HRUNA & HMA & HFA & HVA).
destruct (psl_runB lo hi HrngA) as (HSTAT & HRUNB & HOBL & HJJ & HPCB & HMB & HFB & HVB).
destruct (psl_runL lo hi HrngA) as (HRUNL & HML & HVL).
(* ---- phase A: the head to the inline shadow check (psl_iter's phase A) ---- *)
eapply (fsw_run_to_AJU B fsw_wr_tbl fsw_wr_tbl_ok W FUEL PSL_SHCHK E (psl_head lo hi) (psl_ssA lo hi)
          RS_running ms STK sp0 FP ly S W0 mem0 md0 own lyc Sc U mdc k Q);
  [exact HS | exact HRUNA | exact I | exact HARU | exact HJ | | ].
{ cbn [ss_mem psl_head].
  eapply awr_ok_cons_gen with (k := 22%nat) (b := shF);
    [reflexivity | exact E22 | cbn [psl_sh_region YP09.r_wlo YP09.r_whi]; intros a Ha; apply HAWRsh; lia |].
  apply awr_ok_cons_ro; [cbn [psl_byte_region YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]. }
intros ms1 mat1 HS1 HJ1 HARU1 HF1 HFr1 HG1.
cbn [ms_mem mkst] in HF1, HFr1, HG1, HJ1, HARU1.
assert (MEQ1 : forall a, 0 <= a < 2 ^ 64 -> ~ (shF <= a < shF + 8) ->
  ms_mem ms1 (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)).
{ intros a Ha Hna. apply HF1. rewrite (wz a Ha). intros (rr & Hinr & Hrr).
  cbn [ss_mem psl_head In] in Hinr. destruct Hinr as [<-|[<-|[]]];
    cbn [psl_sh_region psl_byte_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrr;
    rewrite ?E22 in Hrr; lia. }
assert (MEQ1r : forall a, 0 <= a < 2 ^ 64 -> ~ (shF <= a < shF + 8) ->
  mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms1)) a = mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms)) a)
  by (intros a Ha Hna; unfold mbyte, mrestrict; rewrite (MEQ1 a Ha Hna); reflexivity).
assert (HRA1 : range_addressable (aview tfibsegs (w_H W) (ms_mem ms1)) SHADOW_OFF (q + 1) 1).
{ eapply range_addressable_agree; [|exact HRA]. intros x Hx.
  unfold aview, shadow_of_addr. replace x with (q + 1) by lia.
  rewrite (MEQ1r (SHADOW_OFF + (q + 1) / 8) ltac:(unfold SHADOW_OFF in *;
    pose proof (Z.div_le_mono 0 (q + 1) 8 ltac:(lia));
    pose proof (Z.div_le_upper_bound (q + 1) 8 (2 ^ 47) ltac:(lia) ltac:(lia)); lia) HSEPS).
  reflexivity. }
assert (HVAL1 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (q + 1) 1 0).
{ intros i Hi. destruct i as [|i]; [|exfalso; exact (psl_nat_lt1 i Hi)].
  pose proof (HVAL 0%nat Hi) as H0. cbn [Z.of_nat] in H0 |- *. rewrite Z.add_0_r in H0 |- *.
  rewrite (MEQ1r (q + 1) (psl_bd_q64 c q esc shF r lo hi HBD) HSEPB). exact H0. }
(* ---- phase B: the token run over the inline check, without the shadow region ---- *)
assert (HSB : st_ok tfibsegs E (psl_ssB lo hi) (restrict (w_H W) ms1)).
{ pose proof (st_ok_submem tfibsegs E (psl_ssA lo hi) (restrict (w_H W) ms1) [psl_byte_region] HS1
    ltac:(rewrite HMA; apply submem_drop; apply submem_keep;
          [apply subregion_refl | apply submem_nil])
    ltac:(vm_compute; reflexivity)) as HX.
  unfold psl_ssB. rewrite <- HVA. exact HX. }
assert (E24' : ew E 24 = Z_to_bv 64 q)
  by (rewrite <- E24; symmetry; apply Z_to_bv_bv_unsigned).
assert (SHOK : sh_ok tfibsegs fs_Bx psl_SH E (mrestrict (w_H W) (ms_mem ms1))).
{ unfold psl_SH. constructor; [|constructor].
  apply (shent_ok_of_range tfibsegs (w_H W) (ms_mem ms1) E fs_Bx 24%nat (q + 1) 1 q 1 2 HRA1).
  - unfold fs_Bx. apply (U_atom E 32 SHADOW_OFF E32). unfold SHADOW_OFF; lia.
  - apply (U_atom E 24 q E24'). lia.
  - lia.
  - lia.
  - intros x Hx. cbn [Z.min Z.max] in Hx.
    assert (Hxq : x = q + 1) by lia. rewrite Hxq. exact HAPP. }
eapply (fsw_run_tok_AJU B fsw_wr_tbl fsw_wr_tbl_ok W FUEL E psl_K fs_Bx fs_Bspan psl_SH
          (psl_ssB lo hi) (psl_stB lo hi) (TS_stopped (SR_load (Some 24%nat) 1)) ms1
          STK sp0 FP ly S W0 mem0 md0 own lyc Sc U _ k Q);
  [exact HSB | exact SHOK | exact HSTAT | exact HRUNB | exact I | exact HARU1 | exact HJ1
  | rewrite HOBL; apply Forall_nil | | ].
{ cbn [psl_ssB ss_mem].
  apply awr_ok_cons_ro; [cbn [psl_byte_region YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]. }
intros ws ms2 mat2 Hlen HS2 Hsh2 HJ2 HARU2 HF2 HFr2 HG2.
cbn [ms_mem mkst] in HF2, HFr2, HG2, HJ2, HARU2.
rewrite HJJ in Hlen.
destruct ws as [|u1 ws]; [discriminate Hlen|].
destruct ws as [|u2 ws]; [discriminate Hlen|].
destruct ws as [|u3 ws]; [|discriminate Hlen]. clear Hlen.
assert (MEQ2 : forall x, ms_mem ms2 x = ms_mem ms1 x).
{ apply (psl_frame_ro E [psl_byte_region] (ms_mem ms1) (ms_mem ms2));
    [constructor; [cbn [psl_byte_region YP09.r_wlo YP09.r_whi]; lia | constructor]|].
  unfold psl_ssB in HF2; cbn [ss_mem] in HF2; exact HF2. }
set (E2 := extK E psl_K [u1; u2]) in *.
assert (EW2 : forall n, (n < 60)%nat -> ew E2 n = ew E n).
{ intros n Hn. unfold E2, psl_K. cbn [extK].
  rewrite (ew_ewset_other (ewset E 60 u1) 61 u2 n ltac:(lia)), (ew_ewset_other E 60 u1 n ltac:(lia)).
  reflexivity. }
assert (HAT2 : psl_at E2 c q esc shF o r).
{ unfold psl_at.
  rewrite (EW2 18%nat ltac:(lia)), (EW2 21%nat ltac:(lia)), (EW2 22%nat ltac:(lia)),
          (EW2 24%nat ltac:(lia)), (EW2 26%nat ltac:(lia)), (EW2 19%nat ltac:(lia)),
          (EW2 32%nat ltac:(lia)).
  exact HAT. }
(* ---- the cut at the data load: the loaded byte is the terminating zero, seated as atom 33 ---- *)
set (E3 := ewset E2 33 (Z_to_bv 64 0)) in *.
assert (EW3 : forall n, n <> 33%nat -> ew E3 n = ew E2 n)
  by (intros n Hn; unfold E3; apply ew_ewset_other; exact Hn).
assert (E3_33 : ew E3 33 = Z_to_bv 64 0) by (unfold E3; apply ew_ewset_same).
assert (HAG3 : YCeo.env_agree_on (fun n => negb (Nat.eqb n 33)) E2 E3).
{ split; [|unfold E3; apply ed_ewset].
  intros n Hn. apply EW3. intros ->. cbn in Hn. discriminate Hn. }
assert (HS3 : st_ok tfibsegs E3 (sh_ss (psl_stB lo hi)) (restrict (w_H W) ms2))
  by exact (YCeo.st_ok_agree_on tfibsegs _ E2 E3 _ _ HS2 HAG3 (psl_on33 lo hi HrngA)).
assert (HVAL2 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms2)) (q + 1) 1 0).
{ intros i Hi. unfold mbyte, mrestrict. rewrite (MEQ2 (Z_to_bv 64 (q + 1 + Z.of_nat i))).
  exact (HVAL1 i Hi). }
assert (HSC : st_ok tfibsegs E3 (psl_ssC lo hi 0 0) (restrict (w_H W) ms2)).
{ pose proof (st_ok_submem tfibsegs E3 (sh_ss (psl_stB lo hi)) (restrict (w_H W) ms2) [] HS3
    (submem_nil _) ltac:(reflexivity)) as HX1.
  pose proof (st_ok_add_region' tfibsegs E3 _ (restrict (w_H W) ms2) psl_byte_region_c HX1
    ltac:(vm_compute; reflexivity)) as HX2.
  cbn [ms_mem restrict] in HX2.
  assert (HROK : region_ok tfibsegs E3 (mrestrict (w_H W) (ms_mem ms2)) psl_byte_region_c).
  { unfold psl_byte_region_c, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite (EW3 24%nat ltac:(discriminate)), (EW2 24%nat ltac:(lia)), E24.
    split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs E3 _ q 1 1 (SOff 33 0) 0);
      [rewrite fsw_SOff0, E3_33; reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
      | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; exact HVAL2]. }
  pose proof (HX2 HROK I) as HX3.
  pose proof (st_ok_add_fact tfibsegs E3 _ (restrict (w_H W) ms2) 33%nat (mkAF 0 0 0) HX3
    (psl_afact E3 33%nat 0 0 0 ltac:(rewrite E3_33; exact (wz 0 psl_z0))
       (conj (Z.le_refl 0) (Z.le_refl 0)))) as HX4.
  unfold psl_ssC. rewrite HPCB, HFB, HVB in HX4. exact HX4. }
(* the zero byte decides the EQ test: seat it as a condition *)
assert (HSCL : st_ok tfibsegs E3 (psl_ssCL lo hi) (restrict (w_H W) ms2)).
{ unfold psl_ssCL. apply (st_ok_add_cond tfibsegs E3 _ _ BC_EQ (SOff 33 0) (SLit 0) HSC).
  rewrite fsw_SOff0, E3_33, psl_lit_denot. vm_compute. reflexivity. }
(* ---- phase L: from the cut to PSL_END ---- *)
eapply (fsw_run_to_AJU B fsw_wr_tbl fsw_wr_tbl_ok W FUEL PSL_END E3 (psl_ssCL lo hi)
          (psl_ssL lo hi) RS_running ms2 STK sp0 FP ly S W0 mem0 md0 own lyc Sc U _ k Q);
  [exact HSCL | exact HRUNL | exact I | exact HARU2 | exact HJ2 | | ].
{ unfold psl_ssCL, psl_ssC, add_cond, add_atom. cbn [ss_mem].
  apply awr_ok_cons_ro; [cbn [psl_byte_region_c YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]. }
intros ms3 mat3 HS4 HJ4 HARU4 HF4 HFr4 HG4.
cbn [ms_mem mkst] in HF4, HFr4, HG4, HJ4, HARU4.
assert (MEQ3 : forall x, ms_mem ms3 x = ms_mem ms2 x).
{ apply (psl_frame_ro E3 (ss_mem (psl_ssCL lo hi)) (ms_mem ms2) (ms_mem ms3));
    [unfold psl_ssCL, psl_ssC, add_cond, add_atom; cbn [ss_mem];
     constructor; [cbn [psl_byte_region_c YP09.r_wlo YP09.r_whi]; lia | constructor]
    | exact HF4]. }
assert (MEQ31 : forall x, ms_mem ms3 x = ms_mem ms1 x)
  by (intros x; rewrite MEQ3; apply MEQ2).
(* ---- the loop's shift: atom 24 becomes the zero's address q + 1 ---- *)
assert (HAT3 : psl_at E3 c q esc shF o r).
{ unfold psl_at.
  rewrite (EW3 18%nat ltac:(discriminate)), (EW3 21%nat ltac:(discriminate)),
          (EW3 22%nat ltac:(discriminate)), (EW3 24%nat ltac:(discriminate)),
          (EW3 26%nat ltac:(discriminate)), (EW3 19%nat ltac:(discriminate)),
          (EW3 32%nat ltac:(discriminate)).
  exact HAT2. }
assert (HSG : st_ok tfibsegs E3 (mkSS (ss_pc (psl_ssL lo hi)) (ss_regs (psl_ssL lo hi))
                 (ss_mem (psl_ssL lo hi)) (ss_resv (psl_ssL lo hi)) psl_G)
                 (restrict (w_H W) ms3))
  by exact (st_ok_facts tfibsegs E3 _ _ psl_G HS4 (psl_G_ok E3 c q esc shF o r lo hi HAT3 HBD)).
set (E4 := ewset E3 24 (Z_to_bv 64 (q + 1))) in *.
assert (Hq0 : 0 <= q + 1 < 2 ^ 64) by exact (psl_bd_q64 c q esc shF r lo hi HBD).
assert (E4_24 : bv_unsigned (ew E4 24) = q + 1)
  by (unfold E4; rewrite ew_ewset_same; apply wz; exact Hq0).
assert (EW4 : forall n, n <> 24%nat -> ew E4 n = ew E3 n)
  by (intros n Hn; unfold E4; apply ew_ewset_other; exact Hn).
assert (HAT4 : psl_at E4 c (q + 1) esc shF o r).
{ pose proof HAT3 as (A18 & A21 & A22 & A24 & A26 & A19 & A32). unfold psl_at.
  rewrite (EW4 18%nat ltac:(discriminate)), (EW4 21%nat ltac:(discriminate)),
          (EW4 22%nat ltac:(discriminate)), (EW4 26%nat ltac:(discriminate)),
          (EW4 19%nat ltac:(discriminate)), (EW4 32%nat ltac:(discriminate)), E4_24.
  repeat split; assumption. }
assert (HBD4 : psl_bd c (q + 1) esc shF r lo hi)
  by exact (psl_bd_shift c q esc shF r lo hi c lo hi HBD Hq1 (proj1 HBD)).
assert (HSF : st_ok tfibsegs E4 (mkSS PSL_END psl_regsF [psl_byte_regionF] None psl_G) (restrict (w_H W) ms3)).
{ rewrite <- (psl_runLF lo hi HrngA).
  eapply (st_ok_rebase tfibsegs E3 E4 psl_rb _ _ psl_G HSG).
  - exact (psl_rebase_ok E3 E4 q (proj1 (proj2 (proj2 (proj2 HAT3)))) E4_24 EW4
             ltac:(unfold E4; apply ed_ewset)).
  - intros rr n Hinr Hb. rewrite psl_mem_mk, HML in Hinr. cbn [In] in Hinr.
    destruct Hinr as [<-|[]]. cbn [psl_byte_region_c YP09.r_base] in Hb. injection Hb as <-.
    unfold rebase_exact, psl_rb. cbn [rb_lookup Nat.eqb].
    pose proof HAT3 as (_ & _ & _ & A24 & _). rewrite A24, E4_24. ring.
  - exact (psl_G_ok E4 c (q + 1) esc shF o r lo hi HAT4 HBD4). }
(* ---- drop the zero's region; re-seat the four scratch registers; give back the shadow granule ---- *)
pose proof (st_ok_submem tfibsegs E4 _ (restrict (w_H W) ms3) [] HSF (submem_nil _)
  ltac:(reflexivity)) as HSG0.
destruct (psl_reseat PSL_END E4 (restrict (w_H W) ms3) HSG0) as (E5 & HS5 & E5_18 & EW5).
assert (E5_18' : bv_unsigned (ew E5 18) = 0)
  by (rewrite E5_18, (EW4 33%nat ltac:(discriminate)), E3_33; exact (wz 0 psl_z0)).
pose proof (psl_at_scr E4 E5 c 0 (q + 1) esc shF o r HAT4 EW5 E5_18') as HAT5.
pose proof HAT5 as (_ & _ & A22 & _).
assert (HROKs : region_ok tfibsegs E5 (ms_mem (restrict (w_H W) ms3)) psl_sh_region).
{ apply (psl_sh_env E E5); [rewrite A22, E22; reflexivity|].
  apply (psl_region_ok_eq E (ms_mem (restrict (w_H W) ms1)));
    [|exact (fsw_region_nth E (psl_ssA lo hi) (restrict (w_H W) ms1) 0%nat psl_sh_region HS1
             ltac:(rewrite HMA; reflexivity))].
  intros x. cbn [ms_mem restrict]. unfold mrestrict. rewrite (MEQ31 x). reflexivity. }
pose proof (st_ok_add_region' tfibsegs E5 _ (restrict (w_H W) ms3) psl_sh_region HS5
  ltac:(vm_compute; reflexivity) HROKs I) as HS7.
repeat rewrite wvb_collapse in HJ4. repeat rewrite wvb_collapse in HARU4. repeat rewrite wvb_collapse.
apply (KONT ms3 mat3 E5); [exact HS7 | exact HJ4 | exact HARU4 | exact HAT5 |
  | exact (psl_keep6 E E2 E3 E4 E5 EW2 EW3 EW4 EW5)].
intros a Ha Hna. rewrite (MEQ31 (Z_to_bv 64 a)). exact (MEQ1 a Ha Hna).
Qed.

(* ================= 4. the SCAN: induction over the bytes still to scan ================= *)
(* From the head with the current byte c at q and the plain bytes l after it, then the terminating zero at
   q + 1 + length l: length l iterations of psl_iter, then psl_last. The loop makes no call, so the journal's k
   stays; every byte off the frame's shadow granule [shF, shF + 8) is unchanged. *)
Lemma psl_scan : forall (l : list Z) lo hi (E : env) ms STK sp0 FP ly S W0 mem0 md0 own lyc Sc U
    (W : world tfibsegs) mdc k pos q shF c esc o r (Q : world tfibsegs -> config -> Prop),
  psl_rng lo hi ->
  st_ok tfibsegs E (psl_head lo hi) (restrict (w_H W) ms) ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison U (ms_mem ms)) mdc k ->
  ARU tfibsegs B lyc Sc U W (ms_mem ms) mdc ->
  In (0, pos) (frames Sc) -> shF = shadow_addr (frame_addr lyc 0 pos) ->
  psl_at E c q esc shF o r -> psl_bd c q esc shF r lo hi ->
  (forall a, shF <= a < shF + 8 ->
     awr_byte tfibsegs B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (frames S) a) ->
  plain_bytes l -> WriterSpec.bytes_ok l ->
  q + 1 + Z.of_nat (length l) <= 2 ^ 47 - 8 ->
  (forall i, (i <= length l)%nat ->
     psl_cell W (ms_mem ms) shF (q + 1 + Z.of_nat i) (nth i (l ++ [0]) 0)) ->
  (forall ms' mat' E',
     st_ok tfibsegs E' psl_end_ss (restrict (w_H W) ms') ->
     ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison U (ms_mem ms'))
       (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
     ARU tfibsegs B lyc Sc U W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) ->
     psl_at_end E' (q + 1 + Z.of_nat (length l)) esc shF o r ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (shF <= a < shF + 8) ->
        ms_mem ms' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) ->
     (forall n, In n [2%nat; 3%nat; 4%nat; 8%nat; 9%nat; 27%nat] -> ew E' n = ew E n) ->
     SRr tfibsegs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
induction l as [|d l IH];
  intros lo hi E ms STK sp0 FP ly S W0 mem0 md0 own lyc Sc U W mdc k pos q shF c esc o r Q
    HrngA HS HJ HARU Hin HshF HAT HBD HAWRsh HPL HBY Hq HCELL KONT.
- (* the byte at q + 1 is the terminating zero *)
  pose proof (HCELL 0%nat (Nat.le_0_l _)) as HC0. cbn [Z.of_nat nth app] in HC0.
  rewrite Z.add_0_r in HC0. destruct HC0 as (HRA & HVAL & HSB & HSS & HAP).
  cbn [length Z.of_nat] in Hq. rewrite Z.add_0_r in Hq.
  apply (psl_last lo hi E ms STK sp0 FP ly S W0 mem0 md0 own lyc Sc U W mdc k pos q shF c esc o r Q
           HrngA HS HJ HARU Hin HshF HAT HBD HAWRsh HRA HVAL Hq HSB HSS HAP).
  intros ms' mat' E' HS' HJ' HARU' HAT' HM' HK'.
  apply (KONT ms' mat' E' HS' HJ' HARU'); [|exact HM' | exact HK'].
  cbn [length Z.of_nat]. rewrite Z.add_0_r. exact HAT'.
- (* a plain byte d at q + 1, then the rest l *)
  pose proof (Forall_inv HPL) as HPd. pose proof (Forall_inv_tail HPL) as HPl.
  pose proof (Forall_inv HBY) as HBd. pose proof (Forall_inv_tail HBY) as HBl.
  destruct (psl_byte_rng d HPd (proj2 HBd)) as (lo' & hi' & Hrng' & Hd').
  pose proof (HCELL 0%nat (Nat.le_0_l _)) as HC0. cbn [Z.of_nat nth app] in HC0.
  rewrite Z.add_0_r in HC0. destruct HC0 as (HRA0 & HVAL0 & HSB0 & HSS0 & HAP0).
  pose proof (HCELL 1%nat (le_n_S _ _ (Nat.le_0_l (length l)))) as HC1.
  cbn [Z.of_nat Pos.of_succ_nat] in HC1. destruct HC1 as (_ & _ & HSB1 & _).
  destruct (psl_q_step q (length l) Hq) as (Hq1 & Hq').
  apply (psl_iter lo hi lo' hi' E ms STK sp0 FP ly S W0 mem0 md0 own lyc Sc U W mdc k pos q shF c esc o r d Q
           HrngA Hrng' HS HJ HARU Hin HshF HAT HBD HAWRsh HRA0 HVAL0 (psl_d1 d HPd HBd) Hd' Hq1
           (psl_sepB q shF HSB0 HSB1) HSS0 HAP0).
  intros ms1 mat1 E1 HS1 HJ1 HARU1 HAT1 HM1 HK1.
  apply (IH lo' hi' E1 ms1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc U W _ k pos (q + 1) shF d esc o r Q
           Hrng' HS1 HJ1 HARU1 Hin HshF HAT1 (psl_bd_shift c q esc shF r lo hi d lo' hi' HBD Hq1 Hd')
           HAWRsh HPl HBl Hq').
  + (* the remaining cells, carried to the memory the iteration reached *)
    intros i Hi.
    apply (psl_cell_eq W (ms_mem ms) (ms_mem ms1) shF _ _ (psl_cell_rng c q esc shF r lo hi i (length l) HBD Hi Hq')
             HM1).
    pose proof (HCELL (Datatypes.S i) (le_n_S _ _ Hi)) as HCi.
    rewrite <- (psl_addr_succ q i) in HCi. exact HCi.
  + intros ms2 mat2 E2 HS2 HJ2 HARU2 HAT2 HM2 HK2.
    rewrite wvb_collapse in HJ2, HARU2 |- *.
    apply (KONT ms2 mat2 E2 HS2 HJ2 HARU2).
    * rewrite (psl_addr_succ q (length l)) in HAT2. exact HAT2.
    * intros a Ha Hna. rewrite (HM2 a Ha Hna). exact (HM1 a Ha Hna).
    * intros n Hn. rewrite (HK2 n Hn). exact (HK1 n Hn).
Qed.
End W.
