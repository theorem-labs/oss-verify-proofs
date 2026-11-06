(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import MM_syscalls WStr.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import SysStepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg AProto ABase AKit AKit2 ARep ARepKit ARepFrame ARefill_iface RT_stubs
     F_apoison F_acache F_aalloc3 F_ammap F_aensure F_apopulate.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. Local Ltac2 Set LiaHints.tbl := fun () => "0020>56459188277.9 56461269045.1400000400=S2HES2H12H21H".
destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.   (* [comment removed for export] *)
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.
(* [comment removed for export] *)
Local Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ] | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
Local Ltac by_GC GC := rewrite ?GC; cbn [c_mapped_user c_allocated_user c_num_freed c_mapped_free_array c_count cls_set_mapped_user].

(* [comment removed for export] *)
Ltac lrsc_stepA AMO :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      eapply (evtF_step_acc segs RNG);
      [ reflexivity
      | rewrite (stepF_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
        exec_cbv; simp_is_x0; simp_regs; amo_align AMO; rewrite ?Z.eqb_refl; exec_cbv; amo_align AMO; rewrite ?Z.eqb_refl;
        simp_is_x0; simp_regs; vnorm_for i;
        try solve_load; try solve_store; reflexivity
      | solve_accs
      | simp_regs; vnorm_for i; mem_after_store_opt ]
    end end
  end.

Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma sx32_small : forall w : word, bv_unsigned w < 2^31 -> sx32 w = w.
Proof.
  intros w Hw. pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R.
  rewrite <- (Z_to_bv_bv_unsigned w). Local Ltac2 Set LiaHints.tbl := fun () => "0010=51024740434.4000006S2Hw1R".
rewrite sx32_lit by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma aclass_eta0 : forall r, mkAClass (c_mapped_user r) (c_allocated_user r) (c_num_freed r) (c_mapped_free_array r) (c_count r) = r.
Proof. intros []; reflexivity. Qed.

#[using="Type"] Lemma fvals_small : forall au S k, 0 <= au -> 0 <= S -> au + Z.of_nat k * S <= 2^32 ->
  Forall (fun w : word => bv_unsigned w < 2^31) (fvals au S k).
Proof.
  intros au S k AU SZ B. unfold fvals. apply Forall_rev. apply Forall_map. apply Forall_forall. intros j Hj.
  apply in_seq in Hj. Local Ltac2 Set LiaHints.tbl := fun () => "0030>15522612152.1040825276596.9 67690871212.1000000;00?00GS2AU1B2Hj1JS2HjS1B2Hj1J".
rewrite Z.shiftr_div_pow2 by lia.
  assert (J : 0 <= Z.of_nat j * S <= Z.of_nat k * S) by nia.
  rewrite unsigned_lit; [| change (2^4) with 16; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]. change (2^4) with 16. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma u32arr_app : forall m A ws1 ws2,
  u32arr asegs m A ws1 -> u32arr asegs m (A + 4 * Z.of_nat (length ws1)) ws2 -> u32arr asegs m A (ws1 ++ ws2).
Proof.
  intros m A ws1 ws2 [[B0 [B1 B]] [W0 [W1 W]]] [[C0 [C1 C]] [V0 [V1 V]]].
  rewrite u32s_length in B1. rewrite u32s_length in C1.
  split.
  - split; [exact B0|]. Local Ltac2 Set LiaHints.tbl := fun () => "0070>11207107736.171314119977.17 24523600030.2056471022746.2059678491675.2062215688325.207607299229.20 00000:00D00Q00^00k01801BS2B12C12V1S2B12C12V1S2B12C12Hi2GES2B12C12Hi2LTS2B12C12Hi2GES2B12C12Hi2GES2B12C12Hi".
split; [rewrite u32s_app, length_app, !u32s_length; lia|].
    intros i Hi. rewrite u32s_app in Hi |- *. rewrite length_app, !u32s_length in Hi.
    destruct (Nat.lt_ge_cases i (4 * length ws1)) as [LT|GE].
    + rewrite nth_error_app1 by (rewrite u32s_length; exact LT). apply B. rewrite u32s_length. exact LT.
    + rewrite nth_error_app2 by (rewrite u32s_length; exact GE). rewrite u32s_length.
      specialize (C (i - 4 * length ws1)%nat ltac:(rewrite u32s_length; lia)).
      replace (A + 4 * Z.of_nat (length ws1) + Z.of_nat (i - 4 * length ws1)) with (A + Z.of_nat i) in C by lia. exact C.
  - split; [exact W0|]. split; [rewrite length_app; lia|].
    intros i Hi. rewrite length_app in Hi.
    destruct (Z_lt_le_dec i (4 * Z.of_nat (length ws1))) as [LT|GE].
    + apply W. lia.
    + specialize (V (i - 4 * Z.of_nat (length ws1)) ltac:(lia)).
      replace (A + 4 * Z.of_nat (length ws1) + (i - 4 * Z.of_nat (length ws1))) with (A + i) in V by lia. exact V.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma u32arr_skipn : forall m A ws k, u32arr asegs m A ws -> (k <= length ws)%nat ->
  u32arr asegs m (A + 4 * Z.of_nat k) (skipn k ws).
Proof.
  intros m A ws k [[B0 [B1 B]] [W0 [W1 W]]] K. rewrite u32s_length in B1.
  split.
  - Local Ltac2 Set LiaHints.tbl := fun () => "0090>20669055142.1420742520147.1422062391062.1226460940912.1230086211257.1431686757201.1247889518295.1456224120242.1466007307049.1400000900B00H00Q00Z00`00i01201;S2B11K2HiS2B11K2HiS2B11KS2B12W01KS2B11K2HiS2B11KS2B11K2HiS2B11K2HiS2B11K2Hi".
split; [lia|]. split; [rewrite u32s_length, length_skipn; lia|].
    intros i Hi. rewrite u32s_length, length_skipn in Hi.
    specialize (B (4 * k + i)%nat ltac:(rewrite u32s_length; lia)).
    replace (A + Z.of_nat (4 * k + i)) with (A + 4 * Z.of_nat k + Z.of_nat i) in B by lia. rewrite B.
    rewrite <- (firstn_skipn k ws) at 1. rewrite u32s_app, nth_error_app2 by (rewrite u32s_length, length_firstn; lia).
    rewrite u32s_length, length_firstn. f_equal. lia.
  - split; [lia|]. split; [rewrite length_skipn; lia|].
    intros i Hi. rewrite length_skipn in Hi. specialize (W (4 * Z.of_nat k + i) ltac:(lia)).
    replace (A + (4 * Z.of_nat k + i)) with (A + 4 * Z.of_nat k + i) in W by lia. exact W.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma firstn_S_snoc : forall {X} (l : list X) i x, nth_error l i = Some x -> firstn (Datatypes.S i) l = firstn i l ++ [x].
Proof.
  intros X l. induction l as [|y l IH]; intros [|i] x H; cbn in H |- *; try discriminate.
  - injection H as ->. reflexivity.
  - rewrite (IH i x H). reflexivity.
Qed.

Definition getfrom_entry := 0x35f10.
End CANSEC1.
Notation GETFROM_STACK := 640 (only parsing).    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma copy_loop_spec : forall RNG (d : nat) (i n SRC DST : Z) (src ws0 : list word)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : amem),
  d = Z.to_nat (n - i) ->
  0 <= i < n -> length src = Z.to_nat n -> (n <= Z.of_nat (length ws0))%Z ->
  u32arr asegs m SRC src -> Forall (fun w : word => bv_unsigned w < 2^31) src ->
  u32arr asegs m DST (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) ws0) ->
  mem_inv asegs m ->
  0 <= SRC -> SRC + 4 * n < 2^47 -> 0 <= DST -> DST + 4 * Z.of_nat (length ws0) < 2^47 ->
  (SRC + 4 * n <= DST \/ DST + 4 * Z.of_nat (length ws0) <= SRC) ->
  (forall k, 0 <= k < n -> rng RNG (SRC + 4 * k) 4) -> rng RNG DST (4 * n) ->
  evtF asegs RNG (fun ms' => exists a2' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (DST + 4 * n)) a2' (Z_to_bv 64 (DST + 4 * n)) a4 a5 a6 a7
                    s2 s3 (Z_to_bv 64 (SRC + 4 * n)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x36098) fc None m' (seg_rom asegs)
      /\ munch [(DST, DST + 4 * n)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ u32arr asegs m' SRC src /\ u32arr asegs m' DST (src ++ skipn (Z.to_nat n) ws0))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (DST + 4 * n)) a2 (Z_to_bv 64 (DST + 4 * i)) a4 a5 a6 a7
             s2 s3 (Z_to_bv 64 (SRC + 4 * i)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x36084) fc None m (seg_rom asegs)).
Proof.
  intros RNG d. Local Ltac2 Set LiaHints.tbl := fun () => "00K0>10351658949.6214403128707.6414753466635.6417280833900.6417290936988.6419524720221.6219526868180.631998957453.63 21998478119.2 27193795878.6427459629101.6434769693751.6134912167793.6440860951330.654272244234.54 43092379359.6645817309450.6346244107748.7347467794576.645060819074.63 51432752878.2 51452465856.6452250756758.6459151149650.6459310648043.5962280414337.637889767965.63 00000<00J00e01101?01N01]01l01m02<02H02T02`02j03303=03O03[03e04704804D04P04\04i05505AS2HD1I2LS2LDS2HD1I2LS2LD1KS2HD1I2LS2LW2D02D12LD2S02S1S2HD1I2LS2LDS2HD1I2LS2LD1KS2HD1I2LS2LW2LDS2HD1I2LS2LW2LDS2HD1I2LS2D02LDSS2HD1I2LS2LW2LDS2HD1I2LS2LDS2HD1I2LS2LWS2HD1I2LS2LDS2HD2LS2LDS2HD1I2LSS2HD2LS2LDS2HD1I2LS2LW2D12LDS2HD1I2LS2LDS2HD2LS2LDS2HD1I2LS2LW2DJ2LDSS2HD1I2LS2LDS2HD1I2LS2LDS2HD1I2LS2LDS2HD1I2LS3NTHS2HD1I2LS2LDS2HD1I2LS2LD".
induction d as [|d IH]; intros until m; intros HD I LS LW SRCA SM DSTA MI S0 S1 D0 D1 DJ RS RDS; [lia|].
  pose proof (munch_refl [(DST, DST + 4 * n)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  destruct (nth_error src (Z.to_nat i)) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; lia].
  pose proof (proj1 (Forall_forall _ _) SM w (nth_error_In _ _ NTH)) as W31. cbv beta in W31.
  assert (LD : length (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) ws0) = length ws0) by (rewrite length_app, length_firstn, length_skipn; lia).
  pose proof (u32arr_read asegs _ _ src i w (wa (SRC + 4 * i)) SRCA NTH ltac:(lia) eq_refl) as RD.
  pose proof (RS i ltac:(lia)) as RS1.
  step. clear RD RS1.                                    (* [comment removed for export] *)
  rewrite (sx32_small w W31).
  pose proof (u32arr_store_ok asegs m DST _ i (wa (DST + 4 * i)) DSTA ltac:(rewrite LD; lia) eq_refl) as SOK.
  step.                                                  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ ?a (le4 ?v)) _) =>
    let E := lazymatch a with wa ?E => E | Z_to_bv _ ?E => E end in
    pose proof (u32arr_write asegs m DST _ i v DSTA ltac:(rewrite LD; lia)) as DST2;
    replace (DST + 4 * i)%Z with E in DST2 by lia
  end.
  replace (upd (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) ws0) (Z.to_nat i) w)
     with (firstn (Z.to_nat (i + 1)) src ++ skipn (Z.to_nat (i + 1)) ws0) in DST2.
  2:{ rewrite upd_firstn_skipn by (rewrite LD; lia).
      rewrite firstn_app, firstn_firstn, Nat.min_id, length_firstn.
      replace (Z.to_nat i - Nat.min (Z.to_nat i) (length src))%nat with 0%nat by lia. rewrite firstn_O, app_nil_r.
      rewrite skipn_app, length_firstn. replace (Datatypes.S (Z.to_nat i) - Nat.min (Z.to_nat i) (length src))%nat with 1%nat by lia.
      rewrite skipn_skipn. replace (1 + Z.to_nat i)%nat with (Z.to_nat (i + 1)) by lia.
      replace (Z.to_nat (i + 1)) with (Datatypes.S (Z.to_nat i)) at 1 by lia.
      rewrite (firstn_S_snoc _ _ _ NTH), (skipn_all2 (firstn (Z.to_nat i) src)) by (rewrite length_firstn; lia).
      rewrite <- app_assoc. reflexivity. }
  clear DSTA. store_done. try clear SOK.
  zstep. zstep.                                          (* [comment removed for export] *)
  setreg 13 (Z_to_bv 64 (DST + 4 * (i + 1))) ltac:(f_equal; clear; lia).
  setreg 20 (Z_to_bv 64 (SRC + 4 * (i + 1))) ltac:(f_equal; clear; lia).
  step. if_cases K; zify_cond K.                         (* [comment removed for export] *)
  - (* [comment removed for export] *)
    rewrite ?unsigned_lit in K by lia.
    eapply evtF_mono.
    { eapply (IH (i + 1) n SRC DST src ws0); try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try lia. }
    cbv beta. intros ms' (a2' & m' & -> & MU2 & WM2 & MI2 & SR3 & DS3).
    exists a2', m'. split; [reflexivity|].
    split; [eapply munch_trans; [exact MU| exact MU2]|]. split; [eapply wmono_trans; [exact WM| exact WM2]|].
    split; [exact MI2|]. split; [exact SR3| exact DS3].
  - (* [comment removed for export] *)
    rewrite ?unsigned_lit in K by lia. assert (EI : i + 1 = n) by lia.
    apply evtF_done. rewrite EI in DST2 |- *. eexists _, _. split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [assumption|]. rewrite firstn_all2 in DST2 by lia. exact DST2.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gftail_post (rav sp gp tp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) (F : bvmap 5 word) (fc : bv 32)
    (RI FA CHK n base lo : Z) (fl2 chunks0 : list word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (stn' : word) m',
    ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6)
             F (ret_pc rav) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 128, bv_unsigned sp); (RI, RI + 8); (RI + 72, RI + 80); (CHK, CHK + 4 * n)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' RI [C8 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' (RI + 72) [C8 stn']
    /\ u32arr asegs m' FA fl2
    /\ u32arr asegs m' CHK (skipn (Z.to_nat base) fl2 ++ skipn (Z.to_nat n) chunks0).

#[using="Type"] Lemma gf_tail_spec : forall RNG (rav sp gp tp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word)
    (rax t0 t1 t2 s1x a0x a1x a2x a6 a7 s2x s5x s6x s7x s8x s9x s10x s11x t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (RI FA CHK n base lo : Z) (fl2 chunks0 : list word) (stn : word) (fr0 : list byte),
  stk asegs m lo (bv_unsigned sp + -128) -> ATOP <= lo -> lo <= bv_unsigned sp - 128 -> mem_inv asegs m ->
  rw_cells asegs m (bv_unsigned sp + -128)
     [CB 24 fr0; C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 1152921504606846976)] ->
  rw_cells asegs m (RI + 72) [C8 stn] ->
  u32arr asegs m FA fl2 -> length fl2 = Z.to_nat (base + n) -> Forall (fun w : word => bv_unsigned w < 2^31) fl2 ->
  u32arr asegs m CHK chunks0 -> length chunks0 = 16%nat ->
  amo_aligned AD (Z_to_bv 64 RI) = true ->
  0 <= base -> 1 <= n <= 16 ->
  0x10007fff8000 <= FA -> FA + 4 * (base + n) <= ATOP -> 4096 <= CHK -> CHK + 64 <= ATOP -> (FA + 4 * (base + n) <= CHK \/ CHK + 64 <= FA) ->      (* [comment removed for export] *)
  0x10007fff8000 <= RI -> RI + 128 <= ATOP -> (RI + 128 <= CHK \/ CHK + 64 <= RI) -> (RI + 128 <= FA \/ FA + 4 * (base + n) <= RI) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG RI 128 -> (forall k, 0 <= k < base + n -> rng RNG (FA + 4 * k) 4) -> rng RNG CHK 64 ->
  evtF asegs RNG (gftail_post rav sp gp tp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v F fc RI FA CHK n base lo fl2 chunks0 m)
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 RI) s1x a0x a1x a2x (Z_to_bv 64 CHK) (Z_to_bv 64 n) (Z_to_bv 64 base) a6 a7
             s2x (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 FA) s5x s6x s7x s8x s9x s10x s11x t3 t4 t5 t6)
        F (Z_to_bv 64 0x36074) fc None m (seg_rom asegs)).
Proof.
  intros until fr0. intros ST CEIL LO MI FR MTX STN FL LFL FL31 CH LCH AMO B0 N FA0 FA1 CH0 CH1 DJ RI0 RI1 DJ2 DJ3 RIMG RSTK RRI RFA RCH.
  unfold AIMG_HI in *. word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (RI, RI + 8); (RI + 72, RI + 80); (CHK, CHK + 4 * n)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  Local Ltac2 Set LiaHints.tbl := fun () => "01D0?10088628586.10410149639848.2  11077664131.1001162083374.100 1533820803.101 17626616805.10317776320430.10017986021819.93 20437625643.92 20443085596.10121009966951.2  21616083527.7  21773604648.4  22675801219.10222706556809.6  22863571789.1  23929814906.7  24173492464.5  24464059725.4  24559885230.10024997445684.97 24997445688.10225029166211.10125878270241.10126868428163.99 27408782894.1002751427977.103 28479965310.4  28586495624.93 30518562691.10133767231806.91 33890036526.10034261108689.7  34436255511.10334436255511.93 36115622446.10039172636981.0  391966529.5    39411676629.10340091925676.98 40156521056.10342403122015.8  42828922347.10343172633177.93 43987951393.10144158664835.10144833359747.10145310275307.10345310275307.98 46584141497.12 51577315571.10351678667182.10052076332688.10052457676892.4  52565067734.10352565067734.93 53426321609.10253439177267.92 53510313877.99 53767577775.99 55591620116.3  56430152559.7  56802955124.2  56995832584.92 58655119491.10259586081465.10359654587429.92 59907387523.10160634079619.10060971994599.3  61158867591.4  61917199023.99 61937685146.95 63235321900.98 65281479724.10365983638659.1016641830380.93  67157832433.10468304558623.2  736387986.91   8179223683.99  8649922632.12  8653920626.5   9664369056.103 00000500800=00E00J00K00S00\00a00f00i01001601;01?01@01J01R01W01_01d01i01n02602;02C02D02J02R02W02\02d02m03203703?03@03G03L03T03Y03c03k04<04D04I04N04S04X04d04i05105205905>05C05H05M05R05Z05^05e05f05n06306806=06B06G06J06N06V06]06e06n07307807=07B07T07Y07h07o08@S3LFLS1NS3LFLS2LO3LFLS3LFLFS2LO3LFLS3LFL3RI0S3LFLS3LFLS1NS2B02DJS2B01NS3LFLS2HxSS2B01N3DJ3S2B03HkkS3FA0S2LO3LFLS3LFLS3LFLS3LFLS2LO3LFLS3LFLS2LO3LFLFS2B01NS3LFL2HBS3LFLS3LFLS2LO3LFLS2B01N2DJS3LFLS3LFLS2LO3LFLSS1N3DJ2S3LFLS2LO3LFLS3LFLS2B03FA11HS3LFL2HBS4CEIL2LO3LFL3RI1S2LO3LFLS3LFLS3LFLS3LFLS3LFLS4CEIL1N3CH1S3LFLS2LO3LFLFS3CH11HS3LFLS3LFLS3LFLS3LFLS3LFLS2LO3LFLS2B0S1N3DJ2SS2LO3LFLS3LFLS3LFLS3LFLS3LFLS3LFLS1NS2B0S2LO3LFLS3LFL1NS2LO3LFLS3LFL3RI0S3LFLS3LFLS3LFLS3CH0S3LFL2B01N3FA03FA1S3LFLS4CEIL2LO1N3CH1S1N3DJ2S4CEIL2LO3LFL3RI1".
zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 (CHK + 4 * n)) ltac:(rewrite Z.shiftl_mul_pow2 by (clear; lia); f_equal; clear; lia).
  setreg 20 (Z_to_bv 64 (FA + 4 * Z.of_nat (Z.to_nat base) + 4 * 0)) ltac:(rewrite Z.shiftl_mul_pow2 by (clear; lia); f_equal; clear -B0; lia).
  setreg 13 (Z_to_bv 64 (CHK + 4 * 0)) ltac:(f_equal; clear; lia).
  pose proof (u32arr_skipn m FA fl2 (Z.to_nat base) FL ltac:(rewrite LFL; clear -B0 N; lia)) as SRCA.
  eapply evtF_cut.
  { eapply (copy_loop_spec RNG _ 0 n (FA + 4 * Z.of_nat (Z.to_nat base)) CHK (skipn (Z.to_nat base) fl2) chunks0); try reflexivity.
    - clear -N; lia.
    - rewrite length_skipn, LFL. clear -B0 N; lia.
    - rewrite LCH. clear -N; lia.
    - exact SRCA.
    - apply Forall_forall. intros w Hw. apply (proj1 (Forall_forall _ _) FL31 w). rewrite <- (firstn_skipn (Z.to_nat base) fl2). apply in_or_app. right. exact Hw.
    - cbn [Z.to_nat firstn skipn app]. exact CH.
    - exact MI.
    - clear -FA0 B0; lia.
    - clear -FA1 B0 N; lia.
    - clear -CH0; lia.
    - rewrite LCH; clear -CH1; lia.
    - rewrite LCH. clear -DJ B0 N; lia.
    - intros kk Hkk. replace (FA + 4 * Z.of_nat (Z.to_nat base) + 4 * kk) with (FA + 4 * (base + kk)) by (clear -B0; lia). apply RFA. clear -B0 Hkk; lia.
    - eapply rng_sub'; [exact RCH|]. clear -N; lia. }
  cbv beta. intros ms' (a2' & m2 & -> & MU2 & WM2 & MI2 & SR2 & CH2).
  xport FR MU2 WM2 ltac:(clear -SPR CEIL LO CH0 CH1 N; lia).
  xport MTX MU2 WM2 ltac:(clear -DJ2 N; lia).
  xport STN MU2 WM2 ltac:(clear -DJ2 N; lia).
  xport FL MU2 WM2 ltac:(rewrite LFL; clear -DJ N B0; lia).
  pose proof (stk_transport_disjoint asegs _ m m2 _ _ ST MU2 WM2 ltac:(cbn [disjoint_from]; clear -SPR CEIL LO CH0 CH1 N; lia)) as ST2.
  clear ST MI SRCA.
  assert (MUF : munch [(bv_unsigned sp - 128, bv_unsigned sp); (RI, RI + 8); (RI + 72, RI + 80); (CHK, CHK + 4 * n)]%Z m m2).
  { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; clear; intros x Hx; lia. }
  clear MU MU2.
  (* [comment removed for export] *)
  step. zstep.                                                 (* [comment removed for export] *)
  snapshot [(RI, RI + 8); (RI + 72, RI + 80)]%Z MUb WMb.
  box CH2. box FL. clear SR2.
  step.                                                        (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  do 7 zstep. step. do 5 zstep.                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                                  (* [comment removed for export] *)
  zstep. step. if_lit.                                         (* [comment removed for export] *)
  do 7 zstep. step. if_lit.                                    (* [comment removed for export] *)
  lrsc_stepA AMO.                                              (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  lrsc_stepA AMO.                                              (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  do 15 step.                                                  (* [comment removed for export] *)
  carry CH2 MUb WMb ltac:(rewrite length_app, !length_skipn, LFL, LCH; clear -DJ2 N B0; lia).
  carry FL MUb WMb ltac:(rewrite LFL; clear -DJ3 N B0; lia).
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -128) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  apply evtF_done. unfold gftail_post.
  do 16 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MUF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [exact MTX|]. split; [exact STN|]. split; [exact FL|].
  exact CH2.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gfa_take {R} (c n : Z) (k : astate -> bool -> AM R) (KK : astate -> AM R) (st2 : astate) : AM R :=
  if c_num_freed (get_cls st2 c) <? n then aundef_ (UCheck 229) (k st2 false) else KK st2.

Definition gfa_tree {R} (st1 : astate) (c n : Z) (k : astate -> bool -> AM R) (KK : astate -> AM R) : AM R :=
  if n <=? c_num_freed (get_cls st1 c) then gfa_take c n k KK st1
  else populate_free_array st1 c (n - c_num_freed (get_cls st1 c)) (fun st2 ok => if ok then gfa_take c n k KK st2 else k st2 false).

#[using="Type"] Lemma cache_refill_tree_gfa : forall {R} st c (k : astate -> bool -> AM R),
  cache_refill_tree st c k =
  (let st1 := init_cache st in let n := max_count st1 c / 2 in
   gfa_tree st1 c n k (fun st2 => k (put_cls c (cls_set_count (n - 1) (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2) true)).
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Definition getfrom_ret (L : alayout) (RNG : footprint) (sp : word) (st : astate) (c n CHK lo : Z) (fl chunks0 : list word) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let r := get_cls st c in let S := size_of_class c in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  fp_le RNG RNG' /\
  exists mu' mfa' ncnt sj' (stm' stn' : word),
  let nf2 := nf + ncnt in let au2 := au + ncnt * S in
     (* [comment removed for export] *)
     (   mu' = mu
      \/ (nf < n /\ mu < au + (n - nf) * S /\ mu' = mu + rup (au + (n - nf) * S - mu) K_USER_MAP
          /\ rw_cells asegs m' (RB + mu) [CB (Z.to_nat (mu' - mu)) (repeat (Z_to_bv 8 0) (Z.to_nat (mu' - mu)))]
          /\ fill_at m' (shad (RB + mu)) (shlen (mu' - mu)) 0xfa
          /\ rng RNG' (RB + mu) (mu' - mu) /\ rng RNG' (shad (RB + mu)) (shlen (mu' - mu)) /\ fp_bw RNG'))
  /\ mu <= mu' <= K_FREEARR_OFF /\ mu' mod K_USER_MAP = 0
  /\ ((n <= nf /\ ncnt = 0) \/ (nf < n /\ ncnt = (mu' - au) / S)) /\ 0 <= ncnt /\ au2 <= mu'
     (* [comment removed for export] *)
  /\ (   mfa' = mfa
      \/ (mfa < 4 * nf2 /\ mfa' = rup (4 * nf2) K_FREEARR_MAP
          /\ fill_at m' (shad (FA + mfa)) (shlen (mfa' - mfa)) 0xfa
          /\ rng RNG' (FA + mfa) (mfa' - mfa) /\ rng RNG' (shad (FA + mfa)) (shlen (mfa' - mfa)) /\ fp_bw RNG'))
  /\ 4 * nf2 <= mfa' <= K_FREEARR_MAX /\ mfa <= mfa' /\ mfa' mod K_FREEARR_MAP = 0
  /\ n <= nf2
  /\ u32arr asegs m' FA (fl ++ fvals au S (Z.to_nat ncnt))
  /\ junk_at m' (FA + 4 * nf2) (mfa' - 4 * nf2)
     (* [comment removed for export] *)
  /\ get_cls st2 c = mkAClass mu' au2 nf2 mfa' (c_count r)
  /\ (st2 = st \/ st2 = put_cls c (get_cls st2 c) st)
     (* [comment removed for export] *)
  /\ munch [(bv_unsigned sp - GETFROM_STACK, bv_unsigned sp);
            (RB + mu, RB + mu'); (shad (RB + mu), shad (RB + mu) + shlen (mu' - mu));
            (FA + 4 * nf, FA + mfa'); (shad (FA + mfa), shad (FA + mfa) + shlen (mfa' - mfa));
            (al_t L + 2792, al_t L + 2800); (al_t L + 2800, al_t L + 3168);
            (RI, RI + 8); (RI + 16, RI + 56); (RI + 68, RI + 69); (RI + 72, RI + 80);
            (CHK, CHK + 4 * n)]%Z m m'
  /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
     (* [comment removed for export] *)
  /\ rw_cells asegs m' RI [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m' (RI + 16)
       [C8 (Z_to_bv 64 (nf2 - n)); C8 (Z_to_bv 64 mfa'); C8 (Z_to_bv 64 au2); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu'); C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m' (RI + 68) [C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m' (RI + 72) [C8 stn']
  /\ u64arr asegs m' (al_t L + 2800) sj' /\ length sj' = 46%nat
  /\ rw_cells asegs m' (al_t L + 2792) [C8 stm']
  /\ u32arr asegs m' CHK (skipn (Z.to_nat (nf2 - n)) (fl ++ fvals au S (Z.to_nat ncnt)) ++ skipn (Z.to_nat n) chunks0)
  /\ azero m' (shad (RB + mu')) (shlen (K_FREEARR_OFF - mu'))
  /\ azero m' (shad (FA + mfa')) (shlen (K_FREEARR_MAX - mfa'))
  /\ m3_cells L m'.

#[using="Type"] Lemma getfrom_spec : forall RNG {R} (k : astate -> bool -> AM R) (KK : astate -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c n CHK lo : Z) (sj fl chunks0 : list word) (stm stn : word) (fj : list byte),
  let r := get_cls st c in let S := size_of_class c in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - GETFROM_STACK ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (al_t L + 2768) -> a2 = Z_to_bv 64 c -> a3 = Z_to_bv 64 CHK -> a4 = Z_to_bv 64 n ->
  m3_cells L m ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 68) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (RI + 72) [C8 stn] ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m (al_t L + 2792) [C8 stm] ->
  u32arr asegs m FA fl -> length fl = Z.to_nat nf -> Forall (fun w : word => bv_unsigned w < 2^31) fl ->
  rw_cells asegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  u32arr asegs m CHK chunks0 -> length chunks0 = 16%nat ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES -> 1 <= n <= 16 ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  al_t L + 208 <= CHK -> CHK + 64 <= al_t L + 2768 ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      getfrom_ret L RNG sp st c n CHK lo fl chunks0 m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (KK st2)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (gfa_tree st c n k KK)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 getfrom_entry) fc None m (seg_rom asegs)).
Proof.
  intros until fj. cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> -> MC MTX REG EXH STN STATS LSJ STM FL LFL FL31 FJ CH LCH AZU AZF SBE HC N MU MUX MUM AUM NF NFA MFA MFAM
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP CHK0 CHK1 RIMG RSTK RCTX RT RRI RFA CXI TIC KONT. band_lin.   (* [comment removed for export] *)
  pose proof T0 as TB. unfold sclr, KLS in TB.   (* [comment removed for export] *)
  box TCX. box SCX. box TSP.
  pose proof MC as MC0. destruct MC0 as (PC & RC & TI & TK & T88 & TSD & CT & ISB & IREL & ISE & IPRE).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, getfrom_entry in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  pose proof (size_of_class_pos c ltac:(unfold K_NUM_CLASSES; exact HC)) as [SZ SZ32].
  set (S := size_of_class c) in *.
  set (mu := c_mapped_user (get_cls st c)) in *. set (au := c_allocated_user (get_cls st c)) in *.
  set (nf := c_num_freed (get_cls st c)) in *. set (mfa := c_mapped_free_array (get_cls st c)) in *.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (RBE : aregion L c = al_space_beg L + c * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
  assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - GETFROM_STACK, bv_unsigned sp)]%Z m) as MUN.
  pose proof (wmono_refl asegs m) as WM.
  rewrite RBE in AZU. rewrite FAE in FL, FJ, AZF, RFA.
  iprefix.
  Local Ltac2 Set LiaHints.tbl := fun () => "03a0?1044680708.140 11077664131.1391162083375.138 11803370145.13311803370145.13711803370145.13811803370145.13911803370145.14011803370145.14711803370145.18311807744665.11 11807744665.12 11807744665.13 11807744665.17 12546622119.14013081094916.13713238179230.32 14207201439.28 14207201439.32 14453557927.13914765711690.28 14765711690.32 1533820803.139 15517826259.3  1577073154.137 16600962308.14017624464818.13317629982615.14817776320431.13817878780447.2  19108682116.13919491992743.14019545140767.7  19617313304.49 19962478346.17020549713025.20 20661731462.17 21153470338.13921312825509.17021323594502.18221723770584.24 21723770584.28 22165204226.14022177321531.14322177321531.14622179418672.18122179418672.18222264047035.17 22264047035.28 22439364775.13822675801219.14022706556809.5  22706556809.7  22713601064.28 22713601064.32 23044817165.14723044817165.18323954395574.33 24199997281.7  24353579233.7  24559885231.1382458073255.139 24633095682.13924794926247.14025029166211.13925069810328.17 25119608324.14025593949770.6  25878270254.13926278908583.13926868428163.13827408782894.13927728750186.13327728750186.147279719063.5    30198278530.13930475974135.6  30518562691.13930991932130.15 30991932130.16 31145098372.13932649392770.13833152464123.16 33152464123.20 33677903874.14033778973979.13333778973979.14733778973979.18333890036527.13834328904925.13235270809255.13935503307089.4  36115622446.13936367760551.13937156020484.14038692635477.0  38996969702.12839252637125.0  39280637297.0  39374125270.14739374125270.18340091925676.13740399269308.3  41761093716.39 42828922350.13342828922350.14742828922350.18343059266230.12643181512580.13943491506282.13343491506282.14743987951406.13944071307771.28 44071307771.32 44158664835.14044833359747.13944957974294.9  45734444757.13346159990506.13346159990506.14746230876290.13946556098215.14046801997731.3  47870485270.24 47870485270.28 48185458843.1334845396443.133 4845396443.147 4845396443.183 49192305668.13950070787425.7  5021192603.133 5021192603.147 50372678712.4  51418988165.13351418988165.14751678667183.13851781178337.7  52565067731.18352568903288.27 52568903288.30 52568903288.33 52569147371.23 52569147371.28 52569147371.33 52569147371.34 52569147371.35 52569147371.36 52992463466.13352992463466.14753180871875.5  53630829530.28 53630829530.32 53708791826.5  53767577775.13853858151569.28 54013831018.13354013831018.14754263952130.14055220021892.13955338958789.14255338958790.14156170256219.136564231410.7    56428783466.13356428783466.14756662477189.3  57522549927.13757628700040.14 57628700040.23 57743577986.13957954056286.14057964782985.13257965143540.13058026457278.4  58538826602.13358538826602.14758619049802.28 58619049802.32 58655119491.14058985283234.24 58985283234.28 59264840287.28 59264840287.32 59308632045.3  59907387523.14060468873383.13960634079619.13960982670241.7  60997568167.13961228736260.13961862341300.6  61917199023.13861929799858.13361929799985.17061929803692.1376193553363.20  61939782290.18261939782295.14862106300826.14762106300826.18362193956734.13 62194018599.12 62208748595.15 6229635638.28  6229635638.32  63235321900.13663720433767.14163740968706.13063741132671.13264873065057.7  65410990007.2  65491858529.7  65807272962.14065983638659.13966028155702.13766966525323.14466966525323.14766966525323.18266966525323.18367256438148.13867698627762.2  68047011384.6  68296530930.24 68296530930.28 68311701610.13368311701610.1477055476356.139 8179223683.137 8581623554.139 8616689889.7   8806423751.14  8806423751.23  8806423751.7   8931307546.7   9034595641.28  9612232322.139 9664369061.133 9664369061.147 9664369061.183 9689982781.3   00000400500900:00;00<00=00>00?00I00V00k01H01e01f01j01n02102402502A02M02N02S02X02\02h03403803903=03>03B03C03M03l04=04B04X04o05>05M05R05S05X05b05l06H06n06o07007407807@07H07M07W07`07k08608:08;08@08A08B08Z08^08c08g08h08i08m09909E09I09N09T09U09f0:A0:E0:J0:V0:c0:h0:i0:j0;40;80;90;:0;@0;D0;E0;I0;J0;K0;L0;M0;Q0;^0;b0;f0=50=90==0=J0=N0=R0=^0=j0=n0>80>B0>C0>D0>N0>R0>^0>j0>o0?00?10?@0?P0?Q0?R0?S0?]0?a0?l0@<0@L0@M0@`0A50A90AD0AN0BB0C70Cm0D[0EN0FF0GO0H;0I:0IF0IR0IW0Ic0Io0J30J70J;0JG0JS0JX0J\0J`0Jd0Je0Jf0K20K>0K?0K@0KD0KH0KM0KN0KO0KP0KT0K`0Kl0L00L40L50LD0LS0L\0Le0Lk0Ll0Lm0Ln0M90M:0M>0MF0MJ0MQ0M]0Md0N:0NF0NM0NN0NX0Na0Nj0O90OE0OR0OV0OW0OX0OY0Od0Oe0P00P50P60PE0PF0PK0PU0P_0Pc0Ph0Q30Q>0QI0QU0Qa0Qe0Qf0Qk0R60R:0R>0RB0RP0S30S80SL0S`0T=0TAS2HBSS2LOSSSSSSS3LFL4LFL2S4CEIL2LO3CX1S4CEIL2LO2T12HC3RIE1YS4CEIL2LO2HC3SP23RIE3SP12TB1YS4CEIL2LO2HC3MFA3SP23RIE4NEWBSS2HBS2KQS1NS1NSS2HC3SP23RIES2HC3SP23RIESS3SP3S3SPRS2HBS3LFL2NF3MFAS3LFL2NF3MFAS2LOSS2HBSS2NFFS3LFL4LFL2S2HC2MU2NF3MFA3SP13SP23MUB4NEWBS4NEWB3Hkk2Hq3HI4S3SPRS3LFL2NF3NC04NEWB4LFL2S3LFL1N2KP4NEWB4LFL22KQS2HC4CHK13RIE1YS2HC4CHK13RIE1YS3SPRSS3LFLS3LFL4LFL2S3LFL4LFL2S4CEIL2LO3CX11H2HC3SP13RIE1YS4CEIL2LO3CX11H2HC3SP12TB3RIE1Y2Y03CX2SSS2HxS2HxS2HC3SP1S2HC3SP1S3LFLS3LFL4LFL2S1N2NF2KPS4CEIL2LO1HS4CEIL2LO1HS2LOSS3SPRSSS4CEIL2LO2HC3SP13SP23RIES2HBS3MUXS2LOSSS2LOS2HC3SP13RIES2HC3SP13RIES2MUS3SPRS1N2KPSS4CEIL2LO2T14CHK1S2HC3SP14CHK04CHK12TB3RIE1YS2HBS3SPRS2HC3MFA3RIES2HC3RIE4NEWBS3SPRSSS3LFL4LFL2S2LOSSS4MFAMS2LOSS2HBSSSSS2HBS3LFL4LFL22HBS2LOS2LOS4CEIL2LO2HC2MU2NF3SP13SP22T14CHK04CHK12TB3RIE3MUB4NEWB4SHF14SHF24SHF34SHF41Y1HS2HBS2HBS3LFL4LFL22HBS2LOS2HBS2HC3SP13RIES2HC3SP13RIES2LOS4CHK03TICS4CHK03TICSSS3MUB4NCS1S2HBS2HC3SP13RIES2HC3SP13RIES3SPRSSS2HC3MFA4CHK01YS2HC4CHK04NEWB1YSSSS3LFL4LFL2S2HBS4CEIL2LO1HS3LFL2HC3MFA3RIES3LFL2HC3MFA3RIESS3LFL2HC2NF3MFA3RIES3LFL2HC1N3MFA3RIE2KPS2LOS4CEIL2LO1HS3LFL4LFL2S4CEIL2LO2HC1N2MU3SP13SP22T14CHK04CHK12TB3RIE2NF3MFAS4CEIL2LO2HC1N3SP13SP24CHK04CHK12TB3RIE3MUB4SHU14SHU2S4CEIL2LO2HC1N3SP13SP24CHK04CHK12TB3RIE4NEWM4SHU34SHU4S4CEIL2LO2HC1N3SP13SP22T14CHK04CHK12TB3RIE1Y1HS4CEIL2LO2HC1N2NF3MFA3SP13SP22T14CHK04CHK12TB3RIE1YS4CEIL2LO2HC1N2NF3SP13SP22T14CHK04CHK12TB3RIE3NC04NEWB1YS4CEIL2LO2HC1N2MU3SP13SP22T14CHK04CHK12TB3RIE3MUB1Y4SHF24SHU11H4SHF14SHU4S4CEIL2LO2HC3SP22T13RIE3MUB4NEWB4SHF14SHF21HS4CEIL2LO2HC3SP13SP22T12TB3RIE3MUB4NEWB4SHF14SHF21Y2NF3MFA4NEWMS2HC3SP13RIES2HC3SP13RIES3MFAS2HC3SP13RIES2HC3SP13RIES2MUS2LOS2KPS2HC3SP13RIES2HC3SP13RIES3SPRS2HBS2HCS2HCSSS2HC3SP13RIES2HC3SP13RIESSS2HxS2HxS3SPRSSSS2NFS2HC3SP13RIES2HC3SP13RIES2LOS2LOSS2HC4CHK03RIE1YS2HC4CHK03RIE1YS2T14CHK1S2T14CHK1S1N2KNSSSS4CEIL2LO1HSS2HBS2NF3NC0S2LOS3LFL1NS3LFL1N4LFL2S3LFL1NS2HC2MU2NF3MFA3SP13SP2S3LFL1N4LFL2S3LFL1NSS3LFL4LFL2S3Hkk3LO4S3MFA3HkkS4NEWB3Hkk4EnewS2HC3MFA3SP2S2HC3SP24NEWBS2LOSSSS4CEIL2LO1HSS4CEIL2LO1HS3SPRSS4CEIL2LO3SPR1HSS3LFLS3LFL4LFL2S3LFL4LFL2S2HBS3NC0S4CHK04CHK1S2HC4CHK11YS2HC4CHK11YS2HC3SP13RIES2HC3SP13RIES2HBSS3SPRS4CEIL2LO1HS2HxS2HxS2HxS2HC3SP13SP21HS1N3SP14CHK04CHK13CXI3TIC2TB2Y03CX2S3SPRS4CEIL2LO2HC3SP23RIES4CEIL2LO2HC3SP23RIES4CEIL2LO3LFL2HC3SP23RIE4LFL2S2SZ".
carve_frame 128%nat ST.
  (* [comment removed for export] *)
  snapshot [(bv_unsigned sp - 128, bv_unsigned sp)]%Z MUp WMp.
  box MTX. box REG. box EXH. box STN. box STATS. box STM. box FL. box FJ. box CH.
  box TI. box TK. box T88. box TSD. box CT. box ISB. box IREL. box ISE. box IPRE.
  do 14 step.                                                  (* [comment removed for export] *)
  carry MTX MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry REG MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry EXH MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry STN MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry STATS MUp WMp ltac:(rewrite LSJ; clear -SPR CEIL LO T0 T1 TIC TB; lia).
  carry STM MUp WMp ltac:(clear -SPR CEIL LO T0 T1 TIC TB; lia).
  carry FL MUp WMp ltac:(rewrite LFL; clear -SPR CEIL LO SP1 SP2 HC NF MFA; lia).
  carry FJ MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC NF MFA; lia).
  carry CH MUp WMp ltac:(rewrite LCH; clear -SPR CEIL LO T0 T1 CHK0 CHK1 TIC TB; lia).
  carry TI MUp WMp ltac:(clear -SPR CEIL LO; lia). carry TK MUp WMp ltac:(clear -SPR CEIL LO; lia).
  carry T88 MUp WMp ltac:(clear -SPR CEIL LO; lia). carry TSD MUp WMp ltac:(clear -SPR CEIL LO; lia).
  carry CT MUp WMp ltac:(clear -SPR CEIL LO CX0 CX1 CXI; lia). carry ISB MUp WMp ltac:(clear -SPR CEIL LO; lia).
  carry IREL MUp WMp ltac:(clear -SPR CEIL LO; lia). carry ISE MUp WMp ltac:(clear -SPR CEIL LO; lia). carry IPRE MUp WMp ltac:(clear -SPR CEIL LO; lia).
  clear MUp WMp.
  step. step. step.                                            (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  do 9 zstep.                                                  (* [comment removed for export] *)
  do 4 zstep.                                                  (* [comment removed for export] *)
  setreg 8 (Z_to_bv 64 (aregion_info L c)) ltac:(rewrite RIE; apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  setreg 20 (Z_to_bv 64 (al_space_beg L + c * 4294967296 + 3758096384)) ltac:(apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  step.                                                        (* [comment removed for export] *)
  do 5 zstep.                                                  (* [comment removed for export] *)
  zstep. step. if_lit.                                         (* [comment removed for export] *)
  zstep. zstep.                                                (* [comment removed for export] *)
  assert (AMO : amo_aligned AD (Z_to_bv 64 (aregion_info L c)) = true)
    by (apply amo_alignedD_intro; [rewrite RIE; clear -SP1 SP2 HC; lia| rewrite RIE; clear -SP3; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]).
  (* [comment removed for export] *)
  lrsc_stepA AMO.                                              (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  box MUN. snapshot [(aregion_info L c, aregion_info L c + 8)]%Z MUl WMl.
  box CT. box CH. box STATS. box STM.
  lrsc_stepA AMO.                                              (* [comment removed for export] *)
  carry CT MUl WMl ltac:(ub SCX; clear -CX0 CX1 SP1 SP2 HC RIE Y CXI; lia).
  carry CH MUl WMl ltac:(rewrite LCH; ub TSP; clear -T0 T1 SP1 SP2 HC RIE CHK0 CHK1 Y TIC TB; lia).
  carry STATS MUl WMl ltac:(rewrite LSJ; ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  carry STM MUl WMl ltac:(ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  step. if_lit.                                                (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  (* [comment removed for export] *)
  unbox MUN.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (MU01 : munch [(bv_unsigned sp - GETFROM_STACK, bv_unsigned sp); (aregion_info L c, aregion_info L c + 8)]%Z m m1)
      by (eapply munch_trans; [eapply munch_weaken; [| exact MUN] | eapply munch_weaken; [| exact MUl]]; unfold sub_fp; cbn [outside]; clear; intros x Hx; lia)
  end.
  rename WM into WM01. clear MUN MUl WMl.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (AZU1 : azero m1 (shad (al_space_beg L + c * 4294967296 + mu)) (shlen (3758096384 - mu)));
    [ eapply azero_frame; [exact AZU | exact MU01 | exact WM01 |]; intros _; cbn [disjoint_from];
      rewrite shad_div, shlen_div; unfold ASHOFF; clear -SPR CEIL LO SP1 SP2 HC MU MUX RIE; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia |];
    assert (AZF1 : azero m1 (shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)) (shlen (536870912 - mfa)));
    [ eapply azero_frame; [exact AZF | exact MU01 | exact WM01 |]; intros _; cbn [disjoint_from];
      rewrite shad_div, shlen_div; unfold ASHOFF; clear -SPR CEIL LO SP1 SP2 HC MFA NF RIE; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia |];
    assert (MC1 : m3_cells L m1);
    [ eapply m3_cells_frame; [exact MC | exact MU01 | exact WM01 |]; ub SCX; unfold AIMG_HI, AIMG_LO;
      do 2 (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 SP1 SP2 HC RIE Y CXI; lia |]); apply Forall_nil |]
  end.
  clear AZU AZF.
  box MU01.
  step.                                                        (* [comment removed for export] *)
  step. if_cases KP; zify_cond KP; rewrite ?unsigned_lit in KP by (clear -NF NFA MU MUX N; lia).   (* [comment removed for export] *)
  all: cycle 1.
  { (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    snapshot [(aregion_info L c + 16, aregion_info L c + 56)]%Z MUr WMr.
    box CT. box CH. box STATS. box STM.
    step.                                                      (* [comment removed for export] *)
    carry CT MUr WMr ltac:(ub SCX; clear -CX0 CX1 SP1 SP2 HC RIE Y CXI; lia).
    carry CH MUr WMr ltac:(rewrite LCH; ub TSP; clear -T0 T1 SP1 SP2 HC RIE CHK0 CHK1 Y TIC TB; lia).
    carry STATS MUr WMr ltac:(rewrite LSJ; ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
    carry STM MUr WMr ltac:(ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
    step. if_cases KN; zify_cond KN. { exfalso. clear -KN N. rewrite ?unsigned_lit in KN by lia. lia. }   (* [comment removed for export] *)
    unbox MU01.
    eapply evtF_cut.
    { eapply (gf_tail_spec RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) with (lo := lo) (base := nf - n) (fl2 := fl) (chunks0 := chunks0);
      try lazymatch goal with
       | |- stk _ _ _ _ => exact ST
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- mem_inv _ _ => assumption
       | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 72) _ => exact STN
       | |- u32arr _ _ CHK _ => exact CH
       | |- u32arr _ _ _ _ => exact FL
       | |- Forall _ _ => exact FL31
       | |- amo_aligned _ _ = true => exact AMO
       | |- length _ = _ => first [exact LCH | rewrite LFL; clear -KP N; lia]
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ CHK _ => eapply rng_sub'; [exact RT|]; clear -CHK0 CHK1 N; lia
       | |- forall _, _ => intros kk Hkk; eapply rng_sub'; [exact RFA|]; clear -KP N NF MFA Hkk; lia
       | |- _ <= CHK \/ _ => ub TSP; clear -Y T0 T1 SP1 SP2 HC KP N NF MFA RIE CHK0 CHK1 TIC TB; destruct Y as [Y|Y]; [right; lia| left; lia]
       | |- _ \/ _ => right; clear -SP1 SP2 HC KP N NF MFA RIE; lia
       end;
      atop_facts; clear -SPR CEIL LO KP N NF MFA SP1 SP2 HC RIE T0 T1 CHK0 CHK1 TIC TB; lia. }
    cbv beta. intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & stn' & m3 & -> & MU3 & WM3 & MI3 & ST3 & MTX3 & STN3 & FL3 & CH3).
    lazymatch type of MUr with munch _ ?m1 ?m2 =>
    assert (MU13 : munch [(bv_unsigned sp - 128, bv_unsigned sp); (aregion_info L c, aregion_info L c + 8); (aregion_info L c + 16, aregion_info L c + 56);
                          (aregion_info L c + 72, aregion_info L c + 80); (CHK, CHK + 4 * n)]%Z m1 m3)
      by (eapply munch_trans; [eapply munch_weaken; [| exact MUr] | eapply munch_weaken; [| exact MU3]]; unfold sub_fp; cbn [outside]; clear; intros x Hx; lia)
    end.
    pose proof (wmono_trans _ _ _ _ WMr WM3) as WM13. clear MUr WMr.
    xport REG MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
    xport EXH MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
    xport STATS MU3 WM3 ltac:(rewrite LSJ; ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
    xport STM MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
    xport FJ MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N NF MFA Y TIC TB; lia).
    apply evtF_done. unfold gfa_tree, gfa_take. fold nf.
    replace (n <=? nf) with true by (symmetry; apply Z.leb_le; exact KP).
    replace (nf <? n) with false by (symmetry; apply Z.ltb_ge; exact KP).
    eapply KONT.
    unfold getfrom_ret, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP. cbv zeta. fold S mu au nf mfa. rewrite FAE, RBE.
    split; [apply fp_le_refl|].
    exists mu, mfa, 0, sj, stm, stn'.
    replace (nf + 0) with nf by (clear; lia). replace (au + 0 * S) with au by (clear; lia).
    split; [left; reflexivity|]. split; [clear -MU MUX; lia|]. split; [exact MUM|].
    split; [left; split; [exact KP| reflexivity]|]. split; [clear; lia|]. split; [clear -MU; lia|].
    split; [left; reflexivity|]. split; [clear -MFA; lia|]. split; [clear; lia|]. split; [exact MFAM|]. split; [exact KP|].
    split; [cbn [Z.to_nat fvals seq map rev]; rewrite app_nil_r; exact FL3|].
    split; [exists fj; exact FJ|].
    split; [symmetry; apply aclass_eta0|| (destruct (get_cls st c); reflexivity)|].
    split; [left; reflexivity|].
    split. { eapply munch_trans; [eapply munch_weaken; [| exact MU01] | eapply munch_weaken; [| exact MU13]]; unfold sub_fp; cbn [outside]; clear -N MFA NF; intros x Hx; lia. }
    split; [eapply wmono_trans; [exact WM01| exact WM3]|]. split; [exact MI3|]. split; [exact ST3|].
    split; [exact MTX3|]. split; [exact REG|]. split; [exact EXH|]. split; [exact STN3|]. split; [exact STATS|]. split; [exact LSJ|]. split; [exact STM|].
    split; [cbn [Z.to_nat fvals seq map rev]; rewrite app_nil_r; replace (nf - n) with (nf - n) by reflexivity; exact CH3|].
    split. { eapply azero_frame; [exact AZU1 | exact MU13 | exact WM13 |]. intros _; cbn [disjoint_from].
             rewrite shad_div, shlen_div; unfold ASHOFF; ub TSP; clear -SPR CEIL LO SP1 SP2 HC MU MUX RIE T0 T1 CHK0 CHK1 N Y TIC TB; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
    split. { eapply azero_frame; [exact AZF1 | exact MU13 | exact WM13 |]. intros _; cbn [disjoint_from].
             rewrite shad_div, shlen_div; unfold ASHOFF; ub TSP; clear -SPR CEIL LO SP1 SP2 HC MFA NF RIE T0 T1 CHK0 CHK1 N Y TIC TB; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
    eapply m3_cells_frame; [exact MC1 | exact MU13 | exact WM13 |]. ub SCX; ub TCX; unfold AIMG_HI, AIMG_LO.
    do 5 (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 SP1 SP2 HC RIE T0 T1 TIC CHK0 CHK1 N Y Y0 CXI TB; with_band CX0 ltac:(lia) |]). apply Forall_nil. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. step. zstep. step. step.                         (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  apply evtF_done. unfold gfa_tree. fold nf.
  replace (n <=? nf) with false by (symmetry; apply Z.leb_gt; exact KP).
  unbox MU01. name_sp sp (-128).
  eapply populate_spec with (lo := lo) (L := L);
  try lazymatch goal with
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption   (* [comment removed for export] *)
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => rewrite Hsp; exact ST
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- _ <= bv_unsigned _ - _ => rewrite Hsp; clear -LO; lia
       | |- mem_inv _ _ => assumption
       | |- m3_cells _ _ => exact MC1
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- rw_cells _ _ (aregion_info _ _ + 68) _ => exact EXH
       | |- rw_cells _ _ (afreearr _ _ + _) _ => rewrite FAE; exact FJ
       | |- rw_cells _ _ (al_t _ + 2792) _ => exact STM
       | |- u64arr _ _ _ _ => exact STATS
       | |- length _ = _ => exact LSJ
       | |- azero _ (shad (aregion _ _ + _)) _ => rewrite RBE; exact AZU1
       | |- azero _ (shad (afreearr _ _ + _)) _ => rewrite FAE; exact AZF1
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => rewrite Hsp; solve_rng
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ (afreearr _ _ + _) _ => rewrite FAE; eapply rng_sub'; [exact RFA|]; clear -NF MFA; lia
       | |- rng _ _ _ => solve_rng
       | |- @eq word _ _ => first [reflexivity | exact TP | f_equal; clear; lia]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       end.
  all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
            clear KONT; fold S mu au nf mfa; first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM N KP HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TIC CXI TB; lia]).
  (* [comment removed for export] *)
  intros st2 RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' PR.
  unfold populate_ret, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP in PR. cbv zeta in PR. fold S mu au nf mfa in PR. rewrite FAE, RBE in PR.
  destruct PR as (FPLE & mu' & mfa' & ncnt & sj' & stm' & UD & MUB & MUM' & NCE & NC0 & FD & NEWB & NEWM & NEWMOD & AR & JR & ST2E
                  & MU2 & WM2 & MI2 & ST2 & REG2 & EXH2 & STATS2 & LSJ2 & STM2 & AZU2 & AZF2 & MC2).
  box UD. box FD. unname_sp.
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RCTX.
  apply (rng_fp_le _ _ _ _ FPLE) in RT. apply (rng_fp_le _ _ _ _ FPLE) in RRI. apply (rng_fp_le _ _ _ _ FPLE) in RFA.
  assert (GC2 : get_cls st2 c = mkAClass mu' (au + ncnt * S) (nf + ncnt) mfa' (c_count (get_cls st c))) by (rewrite ST2E; apply get_cls_put_cls_eq).
  assert (NCS : au + ncnt * S <= mu' /\ 0 <= ncnt * S).
  { split; [| clear -NC0 SZ; nia]. pose proof NCE as E. clear -E MUB MU NC0 SZ. subst ncnt. Z.div_mod_to_equations. nia. }
  destruct NCS as [NCS1 NCS2].
  assert (SHF : shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa) + shlen (mfa' - mfa) <= 0x10007fff8000
                /\ shad (al_space_beg L + c * 4294967296 + mu) + shlen (mu' - mu) <= 0x10007fff8000
                /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)
                /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + mu)).   (* [comment removed for export] *)
  { rewrite !shad_div, !shlen_div. unfold ASHOFF. clear -SP1 SP2 HC MU MUB MFA NF NEWB NEWM. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  destruct SHF as (SHF1 & SHF2 & SHF3 & SHF4).
  xport FR MU2 WM2 ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 TIC TB SHF3 SHF4; lia).
  xport MTX MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 Y TIC TB SHF3 SHF4; lia).
  xport STN MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 Y TIC TB SHF3 SHF4; lia).
  xport CH MU2 WM2 ltac:(rewrite LCH; ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 CHK0 CHK1 Y TIC TB SHF3 SHF4; lia).
  xport FL MU2 WM2 ltac:(rewrite LFL; ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 Y TIC TB SHF3 SHF4; lia).
  clear ST MI REG EXH STATS STM FJ MC1 AZU1 AZF1 CT TI TK T88 TSD ISB IREL ISE IPRE PC RC.
  pose proof (u32arr_app _ _ _ _ FL ltac:(rewrite LFL, Z2Nat.id by (clear -NF; lia); exact AR)) as FL2.
  assert (LFL2 : length (fl ++ fvals au S (Z.to_nat ncnt)) = Z.to_nat (nf + ncnt)) by (rewrite length_app, fvals_length, LFL; clear -NF NC0; lia).
  assert (FL231 : Forall (fun w : word => bv_unsigned w < 2^31) (fl ++ fvals au S (Z.to_nat ncnt))).
  { apply Forall_app. split; [exact FL31|]. apply fvals_small; [clear -MU; lia | clear -SZ; lia |]. rewrite Z2Nat.id by (clear -NC0; lia). clear -NCS1 MUB; lia. }
  replace (ret_pc (Z_to_bv 64 221644)) with (Z_to_bv 64 221644 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  iprefix.
  step. if_lit.                                                (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  step. if_cases KQ; zify_cond KQ; rewrite ?unsigned_lit in KQ by (clear -NF NC0 N MFA NEWB; lia).   (* [comment removed for export] *)
  { (* [comment removed for export] *)
    apply evtF_done. unfold gfa_take. rewrite GC2. cbn [c_num_freed].
    replace (nf + ncnt <? n) with true by (symmetry; apply Z.ltb_lt; exact KQ).
    rewrite aembed_aundef_. apply implF_ret_unr. }
  step. zstep.                                                 (* [comment removed for export] *)
  snapshot [(aregion_info L c + 16, aregion_info L c + 56)]%Z MUr WMr.
  box CH. box STATS2. box STM2. box FL2. clear FL AR.
  step.                                                        (* [comment removed for export] *)
  carry CH MUr WMr ltac:(rewrite LCH; ub TSP; clear -T0 T1 SP1 SP2 HC RIE CHK0 CHK1 Y TIC TB; lia).
  carry STATS2 MUr WMr ltac:(rewrite LSJ2; ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  carry STM2 MUr WMr ltac:(ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  carry FL2 MUr WMr ltac:(rewrite LFL2; clear -SP1 SP2 HC RIE NF NC0 MFA NEWB; lia).
  step. step.                                                  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (gf_tail_spec RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) with (lo := lo) (base := nf + ncnt - n) (fl2 := fl ++ fvals au S (Z.to_nat ncnt)) (chunks0 := chunks0);
    try lazymatch goal with
       | |- stk _ _ _ _ => exact ST2
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- mem_inv _ _ => assumption
       | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 72) _ => exact STN
       | |- u32arr _ _ CHK _ => exact CH
       | |- u32arr _ _ _ _ => exact FL2
       | |- Forall _ _ => exact FL231
       | |- amo_aligned _ _ = true => exact AMO
       | |- length _ = _ => first [exact LCH | rewrite LFL2; clear -KQ N; f_equal; lia]
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ CHK _ => eapply rng_sub'; [exact RT|]; clear -CHK0 CHK1 N; lia
       | |- forall _, _ => (
             intros kk Hkk; assert (M4 : exists q, mfa = 4 * q) by (exists (mfa / 4); clear -MFAM; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia); destruct M4 as [q Hq];
             with_box FD ltac:(destruct DX as [Enew|(LT & Enew & _ & GR1 & _)];
               [ eapply rng_sub'; [exact RFA|]; clear -Hkk Enew MFA NF NC0 NEWB; lia
               | destruct (Z_lt_le_dec (4 * kk + 3) mfa) as [LO4|HI4];
                 [ eapply rng_sub'; [exact RFA|]; clear -Hkk LO4 MFA NF NC0; lia
                 | eapply rng_sub'; [exact GR1|]; clear -Hkk HI4 MFA NF NC0 NEWB Hq; lia ] ]))
       | |- _ <= CHK \/ _ => ub TSP; clear -Y T0 T1 SP1 SP2 HC KQ N NF NC0 MFA NEWB RIE CHK0 CHK1 TIC TB; destruct Y as [Y|Y]; [right; lia| left; lia]
       | |- _ \/ _ => right; clear -SP1 SP2 HC KQ N NF NC0 MFA NEWB RIE; lia
       | |- u32arr _ _ _ _ => exact FL2
       | |- Forall _ _ => exact FL231
       | |- @eq word _ _ => f_equal; clear; lia
       end;
    try (atop_facts; clear -SPR CEIL LO KQ N NF NC0 MFA NEWB SP1 SP2 HC RIE T0 T1 CHK0 CHK1 TIC TB; lia). }
  cbv beta. intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & stn' & m4 & -> & MU3 & WM3 & MI3 & ST3 & MTX3 & STN3 & FL3 & CH3).
  lazymatch type of MUr with munch _ ?ma ?mb =>
  assert (MU24 : munch [(bv_unsigned sp - 128, bv_unsigned sp); (aregion_info L c, aregion_info L c + 8); (aregion_info L c + 16, aregion_info L c + 56);
                        (aregion_info L c + 72, aregion_info L c + 80); (CHK, CHK + 4 * n)]%Z ma m4)
    by (eapply munch_trans; [eapply munch_weaken; [| exact MUr] | eapply munch_weaken; [| exact MU3]]; unfold sub_fp; cbn [outside]; clear; intros x Hx; lia)
  end.
  pose proof (wmono_trans _ _ _ _ WMr WM3) as WM24. clear MUr WMr.
  xport REG2 MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
  xport EXH2 MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
  xport STATS2 MU3 WM3 ltac:(rewrite LSJ2; ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
  xport STM2 MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
  apply evtF_done. unfold gfa_take. rewrite GC2. cbn [c_num_freed].
  replace (nf + ncnt <? n) with false by (symmetry; apply Z.ltb_ge; exact KQ).
  eapply KONT.
  unfold getfrom_ret, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP. cbv zeta. fold S mu au nf mfa. rewrite FAE, RBE.
  split; [exact FPLE|].
  exists mu', mfa', ncnt, sj', stm', stn'.
  assert (SHU : 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + mu) /\ shad (al_space_beg L + c * 4294967296 + mu') + shlen (3758096384 - mu') <= 0x10007fff8000
                /\ shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa') + shlen (536870912 - mfa') <= 0x10007fff8000
                /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)).
  { rewrite !shad_div, !shlen_div. unfold ASHOFF. clear -SP1 SP2 HC MU MUB MFA NF NEWB NEWM. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  destruct SHU as (SHU1 & SHU2 & SHU3 & SHU4).
  split. { with_box UD ltac:(destruct DX as [(LE & Emu)|(LT & Emu & ZN & FI & G1 & G2 & BW)];
           [ left; exact Emu
           | right; split; [exact KP|]; split; [exact LT|]; split; [exact Emu|];
             split; [| split; [| split; [exact G1| split; [exact G2| exact BW]]]];
             [ eapply cells_frame; [exact ZN | exact MU24 | exact WM24 |]; cbn [disjoint_from cells_size csize Nat.add]; rewrite ?Z2Nat.id by (clear -MUB; lia)
             | eapply fill_frame; [exact FI | exact MU24 | exact WM24 |]; intros _; cbn [disjoint_from] ];
             ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N MU MUB SHU1 SHF2 Y TIC TB SHF3 SHF4; lia ]). }
  split; [exact MUB|]. split; [exact MUM'|].
  split; [right; split; [exact KP| exact NCE]|]. split; [exact NC0|]. split; [exact NCS1|].
  split. { with_box FD ltac:(destruct DX as [(LE & Emfa)|(LT & Emfa & FI & G1 & G2 & BW)];
           [ left; exact Emfa
           | right; split; [exact LT|]; split; [exact Emfa|]; split; [| split; [exact G1| split; [exact G2| exact BW]]];
             eapply fill_frame; [exact FI | exact MU24 | exact WM24 |]; intros _; cbn [disjoint_from];
             ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N MFA NF NEWB NEWM SHF1 SHU4 Y TIC TB; lia ]). }
  split; [exact NEWB|]. split; [exact NEWM|]. split; [exact NEWMOD|]. split; [exact KQ|].
  split; [exact FL3|].
  split. { eapply junk_frame; [exact JR | exact MU24 | exact WM24 |]. intros _; cbn [disjoint_from].
           ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N MFA NF NC0 NEWB NEWM Y TIC TB; lia. }
  split; [exact GC2|].
  split; [right; rewrite GC2; exact ST2E|].
  split. { eapply munch_trans; [eapply munch_weaken; [| exact MU01] | eapply munch_trans; [eapply munch_weaken; [| exact MU2] | eapply munch_weaken; [| exact MU3]]];
           unfold sub_fp; cbn [outside]; clear -N MFA NF NC0 NEWB NEWM MUB KP KQ; intros x Hx; lia. }
  split; [eapply wmono_trans; [exact WM01| eapply wmono_trans; [exact WM2 | exact WM3]]|]. split; [exact MI3|]. split; [exact ST3|].
  split; [exact MTX3|]. split; [exact REG2|]. split; [exact EXH2|]. split; [exact STN3|]. split; [exact STATS2|]. split; [exact LSJ2|]. split; [exact STM2|].
  split; [exact CH3|].
  split. { eapply azero_frame; [exact AZU2 | exact MU24 | exact WM24 |]. intros _; cbn [disjoint_from].
           ub TSP; clear -SPR CEIL LO SP1 SP2 HC MU MUB RIE T0 T1 CHK0 CHK1 N SHU1 SHU2 Y TIC TB; rewrite ?shad_div, ?shlen_div in *; unfold ASHOFF in *; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  split. { eapply azero_frame; [exact AZF2 | exact MU24 | exact WM24 |]. intros _; cbn [disjoint_from].
           ub TSP; clear -SPR CEIL LO SP1 SP2 HC MFA NF NEWB NEWM RIE T0 T1 CHK0 CHK1 N SHU3 SHU4 Y TIC TB; rewrite ?shad_div, ?shlen_div in *; unfold ASHOFF in *; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  eapply m3_cells_frame; [exact MC2 | exact MU24 | exact WM24 |]. ub SCX; ub TCX; unfold AIMG_HI, AIMG_LO.
  do 5 (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 SP1 SP2 HC RIE T0 T1 TIC CHK0 CHK1 N Y Y0 CXI TB; with_band CX0 ltac:(lia) |]). apply Forall_nil.   (* [comment removed for export] *)
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC2.
