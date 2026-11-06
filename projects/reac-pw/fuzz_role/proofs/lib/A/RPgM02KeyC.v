(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; every address measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6, the same loaded bytes): THE KEY COMPARE of
   segment M02's key match, 0x822a8 .. the strcmp wrapper .. 0x822f8 .. 0x82318. Proves no function
   (kind: segment lemma). The shared layer is lib/A/RPgM02KeyBase.v; this file restates none of it.

   THE CODE (capstone over the pinned file):
     0x822a8 addi a1,s5,-1; 0x822ac blt a1,ra (ra = -1 and s5 = m + 1 >= 1, a signed compare: never taken) -> ABS
     0x822b0 a1 := 0x20ee0 (.str.1 "reac.cfg.role"); 0x822b8..0x822cc sd t2,0xf8(s1); sd s11,0xf0(s1);
             mv s11,t3; sd t4,0xe8(s1); sd t5,0xe0(s1); sd t6,0xd8(s1); 0x822d0 jal 0x41ad0 (the wrapper)
     0x822d4 li ra,-1; 0x822d8..0x822f0 the five reloads, li a4,0x68, mv t3,s11; 0x822f4 mv a1,s9;
             0x822f8 bnez a0 -> O 0x821bc (the key is not the role key: the scan goes on at m + 2)
     0x822fc li a0,-1; 0x82300 sd a0,0x118(s1); 0x82304..0x82314 a0 := &ent[m + 1]; 0x82318 is handed on.
   The walk runs with one entry state at 0x822a8 (the real frame as one region, write window [R+0xd8, R+0x100)
   for the five spills) up to the wrapper's entry pc, calls the wrapper through RPgStrcmp.aj_strcmp_at, and
   re-enters at 0x822d4 with the five slots as read-only chunks (and, on the match side, the window
   [R+0x118, R+0x120) of `sd a0,0x118(s1)`). The two sides are split on `strcmp_res c1 c2 = 0` BEFORE the second
   entry state, so that the `bnez` is decided on each side. The key string is the body of entry m of the record,
   read out of the first block through RPgMem.rm_pp_ent; the literal is RPgM02Base.m2_strs's tenth conjunct.
   The only bytes this piece writes are [R+0xd8, R+0x100), [R+0x118, R+0x120) and the wrapper's own stack
   [R - 2 ESTACK, R): all three lie in the segment's write set rs_E2 or below R, so the cut's facts cross them. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import AStrcmpDef.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Accessors Role.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgSeg RPgStrcmp RPgMem RPgCheck RPgCheckStr RPgScanF RPgM02Base RPgM02Tail RPgM02KeyBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section kc. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
(* the strcmp wrapper's contract, at every float state: the cut's float state is not the harness's *)
Hypothesis ASTRCMP : forall fy : YK11.FPState, @astrcmp_realizes fy rc rsegs B 0x41ad0.

Lemma rl_m02_key_cmp : forall (cx : rs_scx rsegs) (POST : world rsegs -> config -> Prop) (inp : list byte)
  (at0 m : nat),
rs_start_M02 rsegs B cx inp ->
@rs_from_O fx rc SK rsegs B MT cx POST (S (S m)) ->
(forall (fx3 : YK11.FPState) ly3 S3 W3 regs3 mem3 md3 (rec : Model.pod_rec) (ent : Model.ent) (a0v : Z),
   @rs_chk_base fx rc SK rsegs B MT cx fx3 rec ly3 S3 W3 regs3 mem3 md3 ->
   rs_role_at rsegs cx rec W3 mem3 ->
   Z.of_nat (length (Layout.pp_bytes rec)) = Layout.PP_SIZE ->
   rs_at_cx rsegs cx W3 mem3 regs3
     (rs_L_chk rsegs cx ++ [(LReg 24, snd (rs_PA rsegs cx rec)); (LReg 10, a0v);
                            (LCell XR 0x28, e_F (x_e rsegs cx)); (LCell XR 0x80, e_pp (x_e rsegs cx))]) ->
   Model.ent_wf ent ->
   val_mem rsegs (mrestrict (w_H W3) mem3) a0v 4 (Model.e_type ent) ->
   val_mem rsegs (mrestrict (w_H W3) mem3) (a0v + 4) 4 (Model.e_size ent) ->
   val_mem rsegs (mrestrict (w_H W3) mem3) (a0v + 8) 4 (Cursor.rd32 (Model.e_body ent)) ->
   range_addressable (aview rsegs (w_H W3) mem3) SHADOW_OFF a0v 16 ->
   4096 <= a0v -> a0v + 16 <= alloc_ceiling ->
   (a0v + 16 <= kLowShadowBeg \/ kHighMemBeg <= a0v) ->
   rs_E0 rec = Role.expect_value ent ->
   snd (rs_PA rsegs cx rec) = snd (rs_E0 rec) -> fst (rs_PA rsegs cx rec) = fst (rs_E0 rec) ->
   SRr rsegs W3 (@cfg_at fx3 rsegs 0x82318 regs3 mem3 md3) POST) ->
@rs_from_KM fx rc SK rsegs B MT cx POST at0 m.
Proof using MTL LAWS ASTRCMP.
intros cx POST inp at0 m Hst HO HKV.
destruct Hst as (Hpre & _).
unfold rs_from_KM. intros fx2 ly2 S2 W2 regs2 mem2 md2 rec kb HKM.
destruct HKM as (Hbase & Hat & Hrole & Hinv & Hrec & Ham & Hm1 & Hnone & Hkey).
pose proof Hbase as (Hcore & Hfxk & Hfsh & Hrom & Hpp & Hwf & Hlenb & Hpod0 & Hpodin & Hpodout).
pose proof Hcore as (HJ0 & Hr234 & Hfr0 & Hperm0 & Hio0 & Hmo0 & HK0).
pose proof (m2_stack B cx Hpre) as (HspR & HR16 & Hrsz & Hwin & Hceil & H46 & Hsp47 & Hsp0al & Hev & Hgp & Htp).
pose proof (m2k_apart B LAWS cx Hpre) as (Hp0 & Hpc & Happ & HF0 & HFc & HFsh & Hceil2 & H46b).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof m2_wx as Hwx. pose proof m2_segs_low as Hsegs.
pose proof (RPgScanF.rk_nent_le rec Hwf) as Hnent.
pose proof (m2k_pp_len rec Hwf) as Hppl.
assert (Hppl' : Z.of_nat (length (Layout.pp_bytes rec)) = 19744) by (rewrite Hppl; reflexivity).
assert (Hreq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
unfold T_SEG_STK, ASTACK in Hwin, Hceil, Hceil2.
unfold Layout.PP_SIZE, kLowShadowBeg, kHighMemBeg in Hpc, Happ.

(* ---------------- the values the cut fixes ---------------- *)
pose proof Hat as Hat'. unfold rs_at_cx, rs_at, rs_L_scan, rs_L_chk in Hat'.
rewrite !Forall_app, !Forall_cons_iff in Hat'.
destruct Hat' as (((A8 & A9 & A19 & A23 & A18 & A22 & C08 & C30 & _) &
                   (A24 & A1 & A26 & A7 & A20 & A28 & A27 & A31 & A29 & A30 & C28 & C80 & _)) &
                  (A10 & A21 & A25 & _)).
cbn [rl_at rl_xv fst snd] in A8, A9, A19, A23, A18, A22, C08, C30,
  A24, A1, A26, A7, A20, A28, A27, A31, A29, A30, C28, C80, A10, A21, A25.
change (Model.Ent 0 0 []) with RPgScanF.rk_d in Hkey, Hnone.
pose proof (RPgScanF.rk_ent_wf_nth rec m Hwf ltac:(lia)) as Hwfk.
pose proof Hwfk as (Htk & Hbk & Hsk).
destruct (m2k_key_of_some _ _ Hkey) as (Hkbeq & Htyk & Hszk & Hnulk).
assert (HbkZ : Z.of_nat (length (Model.e_body (nth m (Model.ents rec) RPgScanF.rk_d)))
             = Model.e_size (nth m (Model.ents rec) RPgScanF.rk_d))
  by (rewrite Hbk; apply Z2Nat.id; lia).
assert (Hblen96 : (length (Model.e_body (nth m (Model.ents rec) RPgScanF.rk_d)) <= 96)%nat).
{ pose proof (m2k_bodies_96 rec Hwf) as HF96. rewrite Forall_forall in HF96.
  apply HF96. apply nth_In. lia. }
assert (Hge0 : 0 <= Model.e_size (nth m (Model.ents rec) RPgScanF.rk_d) - 1) by lia.
assert (Hidx : (Z.to_nat (Model.e_size (nth m (Model.ents rec) RPgScanF.rk_d) - 1)
              < length (Model.e_body (nth m (Model.ents rec) RPgScanF.rk_d)))%nat).
{ rewrite Nat2Z.inj_lt. rewrite HbkZ. rewrite (Z2Nat.id _ Hge0). lia. }
destruct (m2k_cstr_bytes (Model.e_body (nth m (Model.ents rec) RPgScanF.rk_d))
  (Z.to_nat (Model.e_size (nth m (Model.ents rec) RPgScanF.rk_d) - 1)) Hidx Hnulk)
  as (Hkless & Hkin & Hknul).
assert (Hkblen : (length kb < length (Model.e_body (nth m (Model.ents rec) RPgScanF.rk_d)))%nat)
  by (rewrite Hkbeq; exact Hkless).
assert (HPP2 : RPgMem.rm_bytes rsegs (w_H W2) mem2 (e_pp (x_e rsegs cx)) (Layout.pp_bytes rec))
  by (unfold rs_pp_at, rs_u8s in Hpp; exact Hpp).
assert (HppIn : In (e_pp (x_e rsegs cx), Layout.PP_SIZE) (ablocks B ly2 S2)).
{ pose proof Hpre as Hpre0. unfold rs_pre, rl_seg_pre in Hpre0.
  destruct Hpre0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hppin & _).
  exact (Permutation_in _ (Permutation_sym Hperm0) Hppin). }

(* ---------------- the entry state at 0x822a8 ---------------- *)
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (G9 : getr regs2 (9%bv : bv 5) = w64 (e_R (x_e rsegs cx))) by exact A9.
assert (G23 : getr regs2 (23%bv : bv 5) = w64 SHADOW_OFF) by exact A23.
assert (E9 : bv_unsigned (ew (Ereg regs2 (@nil word)) 9) = e_R (x_e rsegs cx)).
{ rewrite (ew_Ereg_nat regs2 (@nil word) 9 (9%bv : bv 5) eq_refl), G9.
  unfold w64. apply unsigned_lit_small. lia. }
assert (E23 : bv_unsigned (ew (Ereg regs2 (@nil word)) 23) = SHADOW_OFF).
{ rewrite (ew_Ereg_nat regs2 (@nil word) 23 (23%bv : bv 5) eq_refl), G23.
  unfold w64, SHADOW_OFF. apply unsigned_lit_small. lia. }
pose proof (m2_entry (fx := fx2) RS_KM [] [m2_frame 0 0x100 0xd8 0x100 []] m2k_facts W2 regs2 (@nil word) mem2
  (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil];
  apply (m2_frame_ok _ W2 mem2 (e_R (x_e rsegs cx)) (x_STK rsegs cx) (x_sp0 rsegs cx) 0 0x100 0xd8 0x100 []);
  [exact E9 | lia | lia | exact Hpres | intros _; lia | apply Forall_nil])
  ltac:(cbn; tauto)
  ltac:(apply (m2k_facts_ok _ (e_R (x_e rsegs cx)) E9 ltac:(lia) HR16 E23))).
remember (Ereg regs2 (@nil word)) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs2 (@nil word)) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs M2_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 ->
  ~ ((e_R (x_e rsegs cx) + 0xd8 <= a < e_R (x_e rsegs cx) + 0x100) \/
     (e_R (x_e rsegs cx) + 0x118 <= a < e_R (x_e rsegs cx) + 0x120) \/
     (e_R (x_e rsegs cx) - 16384 <= a < e_R (x_e rsegs cx))) ->
  aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a) by (intros; reflexivity).
pose proof HJ0 as HJ.
unfold cfg_at. change (w64 RS_KM) with (Z_to_bv 64 RS_KM).

(* 0x822a8 addi a1,s5,-1; stop at the `blt` 0x822ac *)
m2_run m2_awr.
ck_keep ltac:(intros aa Hww; destruct Hww as (rr & Hrr & Hbb); cbv beta in Hbb;
  lazymatch type of Hrr with In _ ?rs0 => let rs' := eval vm_compute in rs0 in change (In rr rs') in Hrr end;
  destruct Hrr as [<- | Hrr]; [|destruct Hrr];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hbb; rewrite E9 in Hbb; lia).
m2_branch Hc.
- (* the taken side is dead: m <? -1 is false for a signed compare *)
  exfalso.
  assert (E21 : ew E 21 = Z_to_bv 64 (Z.of_nat m + 1))
    by (subst E; rewrite (ew_Ereg_nat regs2 (@nil word) 21 (21%bv : bv 5) eq_refl); exact A21).
  assert (E1 : ew E 1 = Z_to_bv 64 (-1))
    by (subst E; rewrite (ew_Ereg_nat regs2 (@nil word) 1 (1%bv : bv 5) eq_refl); exact A1).
  assert (DA : sv_denot E (SOff 21 (-1)) = Z_to_bv 64 (Z.of_nat m)).
  { apply bv_eq. rewrite denot_SOff, E21, !unsigned_lit_small by lia.
    replace (Z.of_nat m + 1 + -1) with (Z.of_nat m) by lia.
    apply zcanon_id. unfold M64. lia. }
  assert (DB : sv_denot E (SOff 1 0) = Z_to_bv 64 (-1)).
  { apply bv_eq. rewrite denot_SOff, E1. vm_compute. reflexivity. }
  assert (HLT : branch_taken BC_LT (Z_to_bv 64 (Z.of_nat m)) (Z_to_bv 64 (-1)) = false).
  { assert (HB1 : bv_signed (Z_to_bv 64 (-1)) = -1) by (vm_compute; reflexivity).
    cbn [branch_taken]. rewrite bv_lts_signed, HB1, signed_lit.
    rewrite (zcanon_id (Z.of_nat m)) by (unfold M64; lia).
    rewrite (swrap64_id (Z.of_nat m)) by (unfold half64; lia).
    apply Z.ltb_ge. lia. }
  rewrite DA, DB, HLT in Hc. discriminate Hc.
- (* 0x822b0 .. 0x822d0: the literal, the five spills and the jal; stop at the wrapper's entry pc *)
  clear Hc.
  m2_run m2_awr.
  ck_keep ltac:(intros aa Hww; destruct Hww as (rr & Hrr & Hbb); cbv beta in Hbb;
    lazymatch type of Hrr with In _ ?rs0 => let rs' := eval vm_compute in rs0 in change (In rr rs') in Hrr end;
    destruct Hrr as [<- | Hrr]; [|destruct Hrr];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hbb; rewrite E9 in Hbb; lia).
  (* the registers and the five slots at the call state *)
  lazymatch goal with HS : st_ok _ ?EE ?ss (restrict ?HH ?mm), HAE : env_agree 32 _ ?EE |- _ =>
    pose proof (cs_eq_of_st_ok _ _ ss mm regs2 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
    pose proof (cs_eq_of_st_ok _ _ ss mm regs2 _
      [7; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 28; 29; 30; 31]%bv HS HAE
      ltac:(vm_compute; reflexivity)) as CS1
  end.
  let R := fresh "R11" in rreg HS (11%bv : bv 5) R.
  let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
  lazymatch goal with HS : st_ok _ ?EE ?ss (restrict ?HH ?mm) |- _ =>
    assert (R27 : getr (ms_regs mm) (27%bv : bv 5) = w64 (e_pp (x_e rsegs cx) + 0x4014))
    by (rewrite (st_ok_restrict_reg rsegs HH EE ss mm (27%bv : bv 5) HS);
        replace (sr_get (ss_regs ss) (27%bv : bv 5)) with (SOff 28 0) by (vm_compute; reflexivity);
        rewrite HE, (ck_atom regs2 (@nil word) 28 (28%bv : bv 5) eq_refl); exact A28);
    assert (HSLOTS : forall (od : Z) (n : nat) (r : bv 5) (v : Z),
      Z.of_nat n = bv_unsigned r ->
      In (YP09.mkChunk od (CVal 8 (SOff n 0))) (YP09.r_chunks (nth 0 (ss_mem ss) (m2_frame 0 0 0 0 []))) ->
      getr regs2 r = w64 v -> 0 <= v < 2 ^ 64 ->
      val_mem rsegs (mrestrict (w_H W2) (ms_mem mm)) (e_R (x_e rsegs cx) + od) 8 v)
    by (intros od n r v Hnr Hin Hv Hvr;
        assert (Hr0 : nth_error (ss_mem ss) 0 = Some (nth 0 (ss_mem ss) (m2_frame 0 0 0 0 [])))
          by (vm_compute; reflexivity);
        pose proof (st_ok_region_nth _ _ _ _ 0 _ HS Hr0) as Hreg;
        lazymatch type of Hreg with region_ok _ _ _ ?rg =>
          let rg' := eval vm_compute in rg in
          change (region_ok rsegs EE (mrestrict (w_H W2) (ms_mem mm)) rg') in Hreg
        end;
        apply (field_of_region _ _ _ _ _ _ _ _ _ od 8 (SOff n 0) v Hreg E9 Hin);
        [ apply bv_eq; rewrite denot_SOff, Z.add_0_r, HE,
            (ew_Ereg_nat regs2 (@nil word) n r Hnr), Hv;
          unfold w64; rewrite !unsigned_lit_small by lia; apply zcanon_id; unfold M64; lia
        | cbn [Z.of_N Z.mul]; lia
        | cbn; lia ]);
    rewrite (st_ok_restrict_mkst rsegs HH EE ss mm HS eq_refl);
    replace (ss_pc ss) with 0x41ad0 by (vm_compute; reflexivity)
  end.
  lazymatch goal with HS : st_ok _ _ _ (restrict _ ?mm) |- _ =>
    remember (ms_mem mm) as memT eqn:HmemT; remember (ms_regs mm) as regsT eqn:HregsT
  end.
  clear HS SHOK HE HAE.
  (* the two strings at the call state *)
  assert (HPPT : RPgMem.rm_bytes rsegs (w_H W2) memT (e_pp (x_e rsegs cx)) (Layout.pp_bytes rec)).
  { apply (RPgMem.rm_bytes_kept rsegs (w_H W2) mem2); [exact HPP2|].
    intros x Hx. rewrite Hppl' in Hx. apply KE; lia. }
  assert (HENT : RPgMem.rm_bytes rsegs (w_H W2) memT
    (e_pp (x_e rsegs cx) + (Layout.OFF_ENT + Layout.ENT_SIZE * Z.of_nat m))
    (Layout.ent_mem (nth m (Model.ents rec) RPgScanF.rk_d))).
  { apply (RPgMem.rm_pp_ent rsegs (Model.buf rec) (Model.is_props rec) (Model.has_params rec)
      (Model.params_struct rec) (Model.ents rec) (Model.corrupt rec)
      (m2k_buf_max rec Hwf) Hnent (m2k_bodies_96 rec Hwf)); [exact HPPT | lia]. }
  assert (HKEYB : forall j, (j < length (Model.e_body (nth m (Model.ents rec) RPgScanF.rk_d)))%nat ->
    aview rsegs (w_H W2) memT (e_pp (x_e rsegs cx) + 0x401c + 104 * Z.of_nat m + Z.of_nat j)
    = Some (bv_unsigned (nth j (Model.e_body (nth m (Model.ents rec) RPgScanF.rk_d)) NUL))).
  { intros j Hj.
    pose proof (RPgMem.rm_bytes_slice rsegs (w_H W2) memT _ _ (8 + j)%nat 1%nat HENT
      ltac:(rewrite (m2k_ent_mem_len _ Hwfk); lia)) as HB.
    rewrite (m2k_ent_key_slice _ j Hwfk Hj) in HB.
    pose proof (proj1 (RPgMem.rm_bytes_aview rsegs _ _ _ _) HB 0%nat ltac:(cbn; lia)) as HA.
    cbn [nth] in HA.
    replace (e_pp (x_e rsegs cx) + (Layout.OFF_ENT + Layout.ENT_SIZE * Z.of_nat m) + Z.of_nat (8 + j)
             + Z.of_nat 0)
      with (e_pp (x_e rsegs cx) + 0x401c + 104 * Z.of_nat m + Z.of_nat j) in HA
      by (unfold Layout.OFF_ENT, Layout.ENT_SIZE; lia).
    exact HA. }
  assert (HCSTRK : cstr_at rsegs W2 memT (e_pp (x_e rsegs cx) + 0x401c + 104 * Z.of_nat m)
    (map (fun x : byte => bv_unsigned x) kb)).
  { split; [|split].
    - intros i Hi. rewrite length_map in Hi.
      assert (Hi0 : 0 <= i) by lia.
      assert (Hji : (Z.to_nat i < length kb)%nat)
        by (rewrite Nat2Z.inj_lt; rewrite (Z2Nat.id i Hi0); lia).
      pose proof (HKEYB (Z.to_nat i) ltac:(exact (Nat.lt_trans _ _ _ Hji Hkblen))) as HK1.
      rewrite (Z2Nat.id i Hi0) in HK1. rewrite HK1.
      f_equal. rewrite RPgMem.rm_nth_map. f_equal.
      rewrite Hkbeq. exact (proj1 (Hkin (Z.to_nat i) ltac:(rewrite <- Hkbeq; exact Hji))).
    - rewrite length_map.
      rewrite (HKEYB (length kb) Hkblen), Hkbeq, Hknul. reflexivity.
    - apply Forall_forall. intros v Hv. apply in_map_iff in Hv. destruct Hv as (b0 & Hb0 & Hin0).
      apply (In_nth _ _ NUL) in Hin0. destruct Hin0 as (j & Hj & Hnth).
      rewrite <- Hb0, <- Hnth. rewrite Hkbeq. rewrite Hkbeq in Hj.
      exact (proj2 (Hkin j Hj)). }
  destruct (m2_strs B MT LAWS cx ly2 S2 W2 regs2 mem2 md2 Hpre Hpodin Hcore)
    as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HLIT & _).
  assert (HTlen : Z.of_nat (length (map (fun x : byte => bv_unsigned x) Role.ROLE_KEY)) = 13)
    by (vm_compute; reflexivity).
  assert (HLITT : rl_cstr rsegs (w_H W2) memT 0x20ee0 (map (fun x : byte => bv_unsigned x) Role.ROLE_KEY)).
  { apply (RPgCheckStr.rl_cstr_kept (w_H W2) mem2 memT 0x20ee0 _
      (e_R (x_e rsegs cx) - 16384) (e_R (x_e rsegs cx) + 0x120));
    [ intros x Hx Hnx; apply KE; [exact Hx | lia] | lia | exact HLIT ]. }
  destruct (str_meet_of_cstr rsegs (map (fun x : byte => bv_unsigned x) kb) W2 memT
    (e_pp (x_e rsegs cx) + 0x401c + 104 * Z.of_nat m)
    (map (fun x : byte => bv_unsigned x) Role.ROLE_KEY) 0x20ee0
    HCSTRK (cstr_at_of_rl_cstr rsegs W2 memT 0x20ee0 _ HLITT))
    as (kk & c1 & c2 & Hmeet & Hkk1 & Hkk2 & Hres).
  rewrite length_map in Hkk1. rewrite HTlen in Hkk2.
  assert (HspT : spZ regsT = e_R (x_e rsegs cx)).
  { rewrite <- HspR. unfold spZ. f_equal. subst regsT.
    etransitivity; [exact (C234 (2%bv : bv 5) ltac:(cbv [In]; left; reflexivity))|].
    exact (Hr234 2 ltac:(lia)). }
  assert (R10 : getr regsT 10 = w64 (e_pp (x_e rsegs cx) + 0x401c + 104 * Z.of_nat m)).
  { subst regsT. etransitivity;
    [exact (CS1 (10%bv : bv 5) ltac:(cbv [In]; right; right; right; left; reflexivity)) | exact A10]. }
  assert (R3 : getr regsT 3 = w64 (as_gp B)).
  { subst regsT. etransitivity; [exact (C234 (3%bv : bv 5) ltac:(cbv [In]; right; left; reflexivity))|].
    etransitivity; [exact (Hr234 3 ltac:(lia)) | exact Hgp]. }
  assert (R4 : getr regsT 4 = w64 (as_tp B)).
  { subst regsT. etransitivity;
    [exact (C234 (4%bv : bv 5) ltac:(cbv [In]; right; right; left; reflexivity))|].
    etransitivity; [exact (Hr234 4 ltac:(lia)) | exact Htp]. }
  (* the wrapper's premises for the two strings *)
  destruct (rl_cstr_args rsegs W2 regsT memT 0x20ee0 _ kk HLITT ltac:(lia)
    ltac:(intros b Hb; rewrite HTlen in Hb; rewrite HspT; unfold ESTACK; lia))
    as (Hy0 & Hyk & Hsy & Hmy & Hry & Hhy).
  pose proof HJ as HJc. pose proof HJc as (HART & _).
  destruct (RPgMem.rm_blk_ra rsegs B ly2 S2 W2 memT _ (e_pp (x_e rsegs cx)) Layout.PP_SIZE
    (e_pp (x_e rsegs cx) + 0x401c + 104 * Z.of_nat m) (kk + 1) HART HppIn ltac:(lia)
    ltac:(rewrite Hreq; unfold Layout.PP_SIZE; lia)) as (Hrx & Hhx).
  assert (Hsx : src_ok rsegs W2 regsT memT (e_pp (x_e rsegs cx) + 0x401c + 104 * Z.of_nat m) (kk + 1)).
  { intros b Hb. destruct HCSTRK as (HC1 & HC2 & _). rewrite length_map in HC1, HC2. split.
    - destruct (Z.eq_dec (b - (e_pp (x_e rsegs cx) + 0x401c + 104 * Z.of_nat m)) (Z.of_nat (length kb)))
        as [Eb|Eb].
      + replace b with (e_pp (x_e rsegs cx) + 0x401c + 104 * Z.of_nat m + Z.of_nat (length kb)) by lia.
        rewrite HC2. discriminate.
      + replace b with (e_pp (x_e rsegs cx) + 0x401c + 104 * Z.of_nat m
                        + (b - (e_pp (x_e rsegs cx) + 0x401c + 104 * Z.of_nat m))) by lia.
        rewrite (HC1 (b - (e_pp (x_e rsegs cx) + 0x401c + 104 * Z.of_nat m)) ltac:(lia)). discriminate.
    - rewrite HspT. unfold ESTACK. unfold Layout.PP_SIZE in *. lia. }
  assert (Hmx : amem_range (e_pp (x_e rsegs cx) + 0x401c + 104 * Z.of_nat m) (kk + 1)).
  { apply amem_range_high; [lia | | unfold Layout.PP_SIZE in *; lia].
    destruct Happ as [Hl|Hr]; [left | right]; lia. }
  (* the call *)
  eapply SRr_bind.
  { apply (@aj_strcmp_at fx2 rc SK rsegs B LAWS m2_segs_low 0x41ad0 (ASTRCMP fx2)
      W2 regsT memT (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
      (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 _ (x_k rsegs cx)
      (e_pp (x_e rsegs cx) + 0x401c + 104 * Z.of_nat m) 0x20ee0 kk c1 c2
      (e_R (x_e rsegs cx) - x_sp0 rsegs cx) (w64 0x822d4));
    [ exact HJc
    | exact R10
    | exact R11
    | lia
    | lia
    | lia
    | unfold Layout.PP_SIZE in *; lia
    | lia
    | exact Hmeet
    | rewrite HspT; lia
    | pose proof (RPgCheckStr.mod16_off (e_R (x_e rsegs cx)) (x_sp0 rsegs cx) 0 HR16 Hsp0al eq_refl) as M16;
      rewrite Z.sub_0_r in M16; exact M16
    | lia
    | unfold ESTACK; lia
    | exact R3
    | exact R4
    | exact R1
    | vm_compute; reflexivity
    | exact Hsx
    | exact Hsy
    | intros a Ha; unfold ESTACK; unfold Layout.PP_SIZE in *; lia
    | intros a Ha; unfold ESTACK; lia
    | exact Hmx
    | exact Hmy
    | exact Hrx
    | apply Hhx; lia
    | exact Hry
    | exact Hhy ]. }
  cbv beta. intros W' c' _ (-> & regs3 & mem3 & md3 & -> & HJ3 & Hpres3 & Hio3 & H10 & HK3 & _).
  assert (K3 : forall a, 0 <= a < 2 ^ 64 ->
    ~ ((e_R (x_e rsegs cx) + 0xd8 <= a < e_R (x_e rsegs cx) + 0x100) \/
       (e_R (x_e rsegs cx) + 0x118 <= a < e_R (x_e rsegs cx) + 0x120) \/
       (e_R (x_e rsegs cx) - 16384 <= a < e_R (x_e rsegs cx))) ->
    aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha Hz. rewrite (HK3 a Ha ltac:(unfold ESTACK; lia)). apply KE; [exact Ha | exact Hz]. }
  (* the five slots at the state after the call *)
  assert (HS31 : val_mem rsegs (mrestrict (w_H W2) mem3) (e_R (x_e rsegs cx) + 0xd8) 8
    (e_pp (x_e rsegs cx) + 0x4018)).
  { eapply (val_mem_kept rsegs (w_H W2) (w_H W2) memT mem3);
    [ intros k Hk; apply HK3; [lia | unfold ESTACK; lia] |].
    apply (HSLOTS 0xd8 31%nat (31%bv : bv 5) (e_pp (x_e rsegs cx) + 0x4018) eq_refl
      ltac:(vm_compute; repeat first [left; reflexivity | right])
      ltac:(exact A31) ltac:(unfold Layout.PP_SIZE in *; lia)). }
  assert (HS30 : val_mem rsegs (mrestrict (w_H W2) mem3) (e_R (x_e rsegs cx) + 0xe0) 8
    (e_pp (x_e rsegs cx) + 0x401c)).
  { eapply (val_mem_kept rsegs (w_H W2) (w_H W2) memT mem3);
    [ intros k Hk; apply HK3; [lia | unfold ESTACK; lia] |].
    apply (HSLOTS 0xe0 30%nat (30%bv : bv 5) (e_pp (x_e rsegs cx) + 0x401c) eq_refl
      ltac:(vm_compute; repeat first [left; reflexivity | right])
      ltac:(exact A30) ltac:(unfold Layout.PP_SIZE in *; lia)). }
  assert (HS29 : val_mem rsegs (mrestrict (w_H W2) mem3) (e_R (x_e rsegs cx) + 0xe8) 8
    (e_pp (x_e rsegs cx) + 0x401c)).
  { eapply (val_mem_kept rsegs (w_H W2) (w_H W2) memT mem3);
    [ intros k Hk; apply HK3; [lia | unfold ESTACK; lia] |].
    apply (HSLOTS 0xe8 29%nat (29%bv : bv 5) (e_pp (x_e rsegs cx) + 0x401c) eq_refl
      ltac:(vm_compute; repeat first [left; reflexivity | right])
      ltac:(exact A29) ltac:(unfold Layout.PP_SIZE in *; lia)). }
  assert (HS27 : val_mem rsegs (mrestrict (w_H W2) mem3) (e_R (x_e rsegs cx) + 0xf0) 8
    (e_pp (x_e rsegs cx) + 0x4014)).
  { eapply (val_mem_kept rsegs (w_H W2) (w_H W2) memT mem3);
    [ intros k Hk; apply HK3; [lia | unfold ESTACK; lia] |].
    apply (HSLOTS 0xf0 27%nat (27%bv : bv 5) (e_pp (x_e rsegs cx) + 0x4014) eq_refl
      ltac:(vm_compute; repeat first [left; reflexivity | right])
      ltac:(exact A27) ltac:(unfold Layout.PP_SIZE in *; lia)). }
  assert (HS7 : val_mem rsegs (mrestrict (w_H W2) mem3) (e_R (x_e rsegs cx) + 0xf8) 8
    (Z.of_nat (length (Model.ents rec)))).
  { eapply (val_mem_kept rsegs (w_H W2) (w_H W2) memT mem3);
    [ intros k Hk; apply HK3; [lia | unfold ESTACK; lia] |].
    apply (HSLOTS 0xf8 7%nat (7%bv : bv 5) (Z.of_nat (length (Model.ents rec))) eq_refl
      ltac:(vm_compute; repeat first [left; reflexivity | right])
      ltac:(exact A7) ltac:(lia)). }
  (* the registers the wrapper kept, back at the cut's values *)
  assert (P9 : getr regs3 (Z_to_bv 5 9) = w64 (e_R (x_e rsegs cx))).
  { etransitivity; [exact (Hpres3 9 ltac:(unfold acallee_saved; lia))|].
    subst regsT. etransitivity;
    [exact (CS1 (9%bv : bv 5) ltac:(cbv [In]; right; right; left; reflexivity)) | exact A9]. }
  assert (P23 : getr regs3 (Z_to_bv 5 23) = w64 SHADOW_OFF).
  { etransitivity; [exact (Hpres3 23 ltac:(unfold acallee_saved; lia))|].
    subst regsT. etransitivity;
    [exact (CS1 (23%bv : bv 5) ltac:(cbv [In]; repeat (first [left; reflexivity | right]))) | exact A23]. }
  assert (P8 : getr regs3 (Z_to_bv 5 8) = w64 (e_S (x_e rsegs cx))).
  { etransitivity; [exact (Hpres3 8 ltac:(unfold acallee_saved; lia))|].
    subst regsT. etransitivity;
    [exact (CS1 (8%bv : bv 5) ltac:(cbv [In]; right; left; reflexivity)) | exact A8]. }
  assert (P18 : getr regs3 (Z_to_bv 5 18) = w64 (e_pod (x_e rsegs cx))).
  { etransitivity; [exact (Hpres3 18 ltac:(unfold acallee_saved; lia))|].
    subst regsT. etransitivity;
    [exact (CS1 (18%bv : bv 5) ltac:(cbv [In]; repeat (first [left; reflexivity | right]))) | exact A18]. }
  assert (P19 : getr regs3 (Z_to_bv 5 19) = w64 (shadow_addr (e_F (x_e rsegs cx)))).
  { etransitivity; [exact (Hpres3 19 ltac:(unfold acallee_saved; lia))|].
    subst regsT. etransitivity;
    [exact (CS1 (19%bv : bv 5) ltac:(cbv [In]; repeat (first [left; reflexivity | right]))) | exact A19]. }
  assert (P22 : getr regs3 (Z_to_bv 5 22) = w64 (e_F (x_e rsegs cx) + 0x180)).
  { etransitivity; [exact (Hpres3 22 ltac:(unfold acallee_saved; lia))|].
    subst regsT. etransitivity;
    [exact (CS1 (22%bv : bv 5) ltac:(cbv [In]; repeat (first [left; reflexivity | right]))) | exact A22]. }
  assert (P20 : getr regs3 (Z_to_bv 5 20) = w64 (Z.of_nat (length (Model.ents rec)) - 1)).
  { etransitivity; [exact (Hpres3 20 ltac:(unfold acallee_saved; lia))|].
    subst regsT. etransitivity;
    [exact (CS1 (20%bv : bv 5) ltac:(cbv [In]; repeat (first [left; reflexivity | right]))) | exact A20]. }
  assert (P21 : getr regs3 (Z_to_bv 5 21) = w64 (Z.of_nat m + 1)).
  { etransitivity; [exact (Hpres3 21 ltac:(unfold acallee_saved; lia))|].
    subst regsT. etransitivity;
    [exact (CS1 (21%bv : bv 5) ltac:(cbv [In]; repeat (first [left; reflexivity | right]))) | exact A21]. }
  assert (P24 : getr regs3 (Z_to_bv 5 24) = w64 (snd (rs_PA rsegs cx rec))).
  { etransitivity; [exact (Hpres3 24 ltac:(unfold acallee_saved; lia))|].
    subst regsT. etransitivity;
    [exact (CS1 (24%bv : bv 5) ltac:(cbv [In]; repeat (first [left; reflexivity | right]))) | exact A24]. }
  assert (P25 : getr regs3 (Z_to_bv 5 25) = w64 (Z.of_nat m + 2)).
  { etransitivity; [exact (Hpres3 25 ltac:(unfold acallee_saved; lia))|].
    subst regsT. etransitivity;
    [exact (CS1 (25%bv : bv 5) ltac:(cbv [In]; repeat (first [left; reflexivity | right]))) | exact A25]. }
  assert (P26 : getr regs3 (Z_to_bv 5 26) = w64 8).
  { etransitivity; [exact (Hpres3 26 ltac:(unfold acallee_saved; lia))|].
    subst regsT. etransitivity;
    [exact (CS1 (26%bv : bv 5) ltac:(cbv [In]; repeat (first [left; reflexivity | right]))) | exact A26]. }
  assert (P27 : getr regs3 (Z_to_bv 5 27) = w64 (e_pp (x_e rsegs cx) + 0x4014)).
  { etransitivity; [exact (Hpres3 27 ltac:(unfold acallee_saved; lia))|].
    subst regsT. exact R27. }
  assert (Hsp3 : spZ regs3 = e_R (x_e rsegs cx))
    by (rewrite (m2k_sp_pres _ _ Hpres3); exact HspT).
  (* rs_core at the state after the call *)
  assert (Hcore3 : rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs3 mem3 md3).
  { apply (m2_core_step B MT MTL cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 regs3 mem3 md3
      Hcore HJ3);
    [ intros r Hr; etransitivity;
      [ exact (Hpres3 r ltac:(unfold acallee_saved; lia))
      | subst regsT; exact (C234 (Z_to_bv 5 r)
          ltac:(destruct Hr as [-> | [-> | ->] ]; cbv [In];
                repeat (first [left; apply bv_eq; reflexivity | right]))) ]
    | reflexivity | apply Permutation_refl
    | eapply same_io_trans; [kio | exact Hio3]
    | apply (mo_le_refl MT MTL) |].
    intros a Ha Hs He. apply K3; [exact Ha|].
    intros [Hz|[Hz|Hz]].
    - apply He. unfold rs_E2. left. unfold rl_inw. cbn [hi_w2 role_himg_A].
      rewrite !Exists_cons, Exists_nil. cbn [rl_xv fst snd]. lia.
    - apply He. unfold rs_E2. left. unfold rl_inw. cbn [hi_w2 role_himg_A].
      rewrite !Exists_cons, Exists_nil. cbn [rl_xv fst snd]. lia.
    - apply Hs. rewrite HspR. unfold T_SEG_STK, ASTACK. lia. }
  clear HSLOTS HPPT HENT HKEYB HCSTRK HLITT Hsx Hmx Hrx Hhx Hsy Hmy Hry Hhy HJc HART.
  clear HmemT HregsT R10 R11 R1 R27 CS1 C234 HspT KE HJ.
  (* ---------------- the two sides of the compare ---------------- *)
  assert (E9b : bv_unsigned (ew (Ereg regs3
      [w64 (e_pp (x_e rsegs cx) + 0x4018); w64 (e_pp (x_e rsegs cx) + 0x401c);
       w64 (e_pp (x_e rsegs cx) + 0x401c); w64 (e_pp (x_e rsegs cx) + 0x4014);
       w64 (Z.of_nat (length (Model.ents rec)))]) 9) = e_R (x_e rsegs cx)).
  { rewrite (ew_Ereg_nat regs3 _ 9 (9%bv : bv 5) eq_refl).
    assert (G : getr regs3 (9%bv : bv 5) = w64 (e_R (x_e rsegs cx))) by exact P9.
    rewrite G. unfold w64. apply unsigned_lit_small. lia. }
  assert (E23b : bv_unsigned (ew (Ereg regs3
      [w64 (e_pp (x_e rsegs cx) + 0x4018); w64 (e_pp (x_e rsegs cx) + 0x401c);
       w64 (e_pp (x_e rsegs cx) + 0x401c); w64 (e_pp (x_e rsegs cx) + 0x4014);
       w64 (Z.of_nat (length (Model.ents rec)))]) 23) = SHADOW_OFF).
  { rewrite (ew_Ereg_nat regs3 _ 23 (23%bv : bv 5) eq_refl).
    assert (G : getr regs3 (23%bv : bv 5) = w64 SHADOW_OFF) by exact P23.
    rewrite G. unfold w64, SHADOW_OFF. apply unsigned_lit_small. lia. }
  assert (CH : forall (j : nat) (v : Z) (od : Z), 0 <= v < 2 ^ 64 ->
    nth j [w64 (e_pp (x_e rsegs cx) + 0x4018); w64 (e_pp (x_e rsegs cx) + 0x401c);
           w64 (e_pp (x_e rsegs cx) + 0x401c); w64 (e_pp (x_e rsegs cx) + 0x4014);
           w64 (Z.of_nat (length (Model.ents rec)))] (Z_to_bv 64 0) = w64 v ->
    val_mem rsegs (mrestrict (w_H W2) mem3) (e_R (x_e rsegs cx) + od) 8 v ->
    YP09.chunk_ok rsegs (Ereg regs3
      [w64 (e_pp (x_e rsegs cx) + 0x4018); w64 (e_pp (x_e rsegs cx) + 0x401c);
       w64 (e_pp (x_e rsegs cx) + 0x401c); w64 (e_pp (x_e rsegs cx) + 0x4014);
       w64 (Z.of_nat (length (Model.ents rec)))]) (mrestrict (w_H W2) mem3) (e_R (x_e rsegs cx))
      (YP09.mkChunk od (CVal 8 (SOff (32 + j) 0)))).
  { intros j v od Hv Hnth Hval.
    apply (chunk_ok_val rsegs _ _ _ od 8 (SOff (32 + j) 0) v); [|cbn [Z.of_N Z.mul]; lia | cbn; lia | exact Hval].
    apply bv_eq. rewrite denot_SOff, Z.add_0_r, ew_Ereg_extra, Hnth.
    unfold w64. rewrite !unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
  destruct (Z.eq_dec (strcmp_res c1 c2) 0) as [Heq0|Hne0].
  + (* ---------------- the key IS the role key: on to the value dispatch ---------------- *)
    assert (Hkbrole : kb = Role.ROLE_KEY)
      by (apply m2k_map_bv_inj; exact (proj1 Hres Heq0)).
    assert (H10' : getr regs3 (10%bv : bv 5) = w64 0) by (rewrite H10, Heq0; reflexivity).
    pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3b & _).
    pose proof (m2_entry (fx := fx2) 0x822d4 [((10%bv : bv 5), SLit 0)]
      [m2_frame 0 0x100 0 0 [YP09.mkChunk 0xd8 (CVal 8 (SOff 32 0)); YP09.mkChunk 0xe0 (CVal 8 (SOff 33 0));
                             YP09.mkChunk 0xe8 (CVal 8 (SOff 34 0)); YP09.mkChunk 0xf0 (CVal 8 (SOff 35 0));
                             YP09.mkChunk 0xf8 (CVal 8 (SOff 36 0))];
       m2_frame 0x100 0x138 0x118 0x120 []]
      m2k_facts W2 regs3
      [w64 (e_pp (x_e rsegs cx) + 0x4018); w64 (e_pp (x_e rsegs cx) + 0x401c);
       w64 (e_pp (x_e rsegs cx) + 0x401c); w64 (e_pp (x_e rsegs cx) + 0x4014);
       w64 (Z.of_nat (length (Model.ents rec)))] mem3) as HS.
    specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil]; cbn [fst snd]; split;
      [ intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz
      | rewrite ck_lit; symmetry; exact H10' ])
      ltac:(vm_compute; reflexivity)).
    specialize (HS ltac:(apply Forall_cons;
      [ apply (m2_frame_ok _ W2 mem3 (e_R (x_e rsegs cx)) (x_STK rsegs cx) (x_sp0 rsegs cx) 0 0x100 0 0);
        [exact E9b | lia | lia | exact Hpres3b | intros Hcc; lia |];
        repeat apply Forall_cons; try apply Forall_nil;
        [ exact (CH 0%nat (e_pp (x_e rsegs cx) + 0x4018) 0xd8 ltac:(unfold Layout.PP_SIZE in *; lia)
            ltac:(reflexivity) HS31)
        | exact (CH 1%nat (e_pp (x_e rsegs cx) + 0x401c) 0xe0 ltac:(unfold Layout.PP_SIZE in *; lia)
            ltac:(reflexivity) HS30)
        | exact (CH 2%nat (e_pp (x_e rsegs cx) + 0x401c) 0xe8 ltac:(unfold Layout.PP_SIZE in *; lia)
            ltac:(reflexivity) HS29)
        | exact (CH 3%nat (e_pp (x_e rsegs cx) + 0x4014) 0xf0 ltac:(unfold Layout.PP_SIZE in *; lia)
            ltac:(reflexivity) HS27)
        | exact (CH 4%nat (Z.of_nat (length (Model.ents rec))) 0xf8 ltac:(lia)
            ltac:(reflexivity) HS7) ]
      | apply Forall_cons; [|apply Forall_nil];
        apply (m2_frame_ok _ W2 mem3 (e_R (x_e rsegs cx)) (x_STK rsegs cx) (x_sp0 rsegs cx)
                 0x100 0x138 0x118 0x120 []);
        [exact E9b | lia | lia | exact Hpres3b | intros _; lia | apply Forall_nil] ])
      ltac:(unfold m2_frame; repeat split; try exact I; unfold extent_disjoint;
            cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite E9b; left; lia)
      ltac:(apply (m2k_facts_ok _ (e_R (x_e rsegs cx)) E9b ltac:(lia) HR16 E23b))).
    remember (Ereg regs3
      [w64 (e_pp (x_e rsegs cx) + 0x4018); w64 (e_pp (x_e rsegs cx) + 0x401c);
       w64 (e_pp (x_e rsegs cx) + 0x401c); w64 (e_pp (x_e rsegs cx) + 0x4014);
       w64 (Z.of_nat (length (Model.ents rec)))]) as E3 eqn:HE3.
    assert (HAE : env_agree 32 (Ereg regs3
      [w64 (e_pp (x_e rsegs cx) + 0x4018); w64 (e_pp (x_e rsegs cx) + 0x401c);
       w64 (e_pp (x_e rsegs cx) + 0x401c); w64 (e_pp (x_e rsegs cx) + 0x4014);
       w64 (Z.of_nat (length (Model.ents rec)))]) E3) by (subst E3; apply env_agree_refl).
    assert (SHOK : sh_ok rsegs M2_Bx [] E3 (mrestrict (w_H W2) mem3)) by constructor.
    assert (KE : forall a, 0 <= a < 2 ^ 64 ->
      ~ ((e_R (x_e rsegs cx) + 0xd8 <= a < e_R (x_e rsegs cx) + 0x100) \/
         (e_R (x_e rsegs cx) + 0x118 <= a < e_R (x_e rsegs cx) + 0x120) \/
         (e_R (x_e rsegs cx) - 16384 <= a < e_R (x_e rsegs cx))) ->
      aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem3 a) by (intros; reflexivity).
    pose proof HJ3 as HJ.
    change (w64 0x822d4) with (Z_to_bv 64 0x822d4).
    m2_run_to m2_awr 0x82318.
    ck_keep ltac:(intros aa Hww; destruct Hww as (rr & Hrr & Hbb); cbv beta in Hbb;
      lazymatch type of Hrr with In _ ?rs0 => let rs' := eval vm_compute in rs0 in change (In rr rs') in Hrr end;
      repeat (destruct Hrr as [<- | Hrr];
        [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hbb;
         first [lia | (rewrite E9b in Hbb; lia)] | ]); destruct Hrr).
    (* the state at 0x82318 *)
    assert (E21b : ew E3 21 = Z_to_bv 64 (Z.of_nat m + 1))
      by (subst E3; rewrite (ew_Ereg_nat regs3 _ 21 (21%bv : bv 5) eq_refl); exact P21).
    assert (E27b : ew E3 27 = Z_to_bv 64 (e_pp (x_e rsegs cx) + 0x4014))
      by (subst E3; rewrite (ew_Ereg_nat regs3 _ 27 (27%bv : bv 5) eq_refl); exact P27).
    lazymatch goal with HS : st_ok _ ?EE ?ss (restrict ?HH ?mm), HAE : env_agree 32 _ ?EE |- _ =>
      pose proof (cs_eq_of_st_ok _ _ ss mm regs3 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234b;
      pose proof (cs_eq_of_st_ok _ _ ss mm regs3 _ [8; 9; 18; 19; 22; 23; 24]%bv HS HAE
        ltac:(vm_compute; reflexivity)) as CS2;
      assert (RA0 : getr (ms_regs mm) (10%bv : bv 5) = sv_denot EE
        (SAlu ALU_ADD (SOff 27 0) (SMd M_MULHU (SAlu ALU_SLL (SOff 21 0) (SLit 32)) (SLit 446676598784))))
      by (refine (eq_trans (st_ok_restrict_reg rsegs HH EE ss mm (10%bv : bv 5) HS)
                   (f_equal (sv_denot EE) _)); vm_compute; reflexivity);
      rewrite (st_ok_restrict_mkst rsegs HH EE ss mm HS eq_refl);
      replace (ss_pc ss) with 0x82318 by (vm_compute; reflexivity)
    end.
    lazymatch goal with HS : st_ok _ _ _ (restrict _ ?mm) |- _ =>
      remember (ms_mem mm) as mem5 eqn:Hmem5; remember (ms_regs mm) as regs5 eqn:Hregs5
    end.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?md) _ => remember md as md5 eqn:Hmd5 end.
    assert (K5 : forall a, 0 <= a < 2 ^ 64 ->
      ~ ((e_R (x_e rsegs cx) + 0xd8 <= a < e_R (x_e rsegs cx) + 0x100) \/
         (e_R (x_e rsegs cx) + 0x118 <= a < e_R (x_e rsegs cx) + 0x120) \/
         (e_R (x_e rsegs cx) - 16384 <= a < e_R (x_e rsegs cx))) ->
      aview rsegs (w_H W2) mem5 a = aview rsegs (w_H W2) mem2 a).
    { intros a Ha Hz. rewrite (KE a Ha Hz). exact (K3 a Ha Hz). }
    assert (K5w : forall a, ~ m2k_wz cx a -> aview rsegs (w_H W2) mem5 a = aview rsegs (w_H W2) mem2 a).
    { intros a Hz. apply K5; unfold m2k_wz, T_SEG_STK, ASTACK in Hz; lia. }
    assert (Hcore5 : rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs5 mem5 md5).
    { apply (m2_core_step B MT MTL cx (rs_E2 rsegs cx) ly2 S2 W2 regs3 mem3 md3 ly2 S2 W2 regs5 mem5 md5
        Hcore3 ltac:(subst mem5 md5; exact HJ));
      [ intros r Hr; subst regs5; exact (C234b (Z_to_bv 5 r)
          ltac:(destruct Hr as [-> | [-> | ->] ]; cbv [In];
                repeat (first [left; apply bv_eq; reflexivity | right])))
      | reflexivity | apply Permutation_refl | rewrite Hmd5; kio | apply (mo_le_refl MT MTL) |].
      intros a Ha Hs He. apply KE; [exact Ha|].
      intros [Hz|[Hz|Hz]].
      - apply He. unfold rs_E2. left. unfold rl_inw. cbn [hi_w2 role_himg_A].
        rewrite !Exists_cons, Exists_nil. cbn [rl_xv fst snd]. lia.
      - apply He. unfold rs_E2. left. unfold rl_inw. cbn [hi_w2 role_himg_A].
        rewrite !Exists_cons, Exists_nil. cbn [rl_xv fst snd]. lia.
      - apply Hs. rewrite HspR. unfold T_SEG_STK, ASTACK. lia. }
    destruct (m2k_chk_kept B MT LAWS cx rec fx2 fx2 ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 regs5 mem5 md5
      Hpre Hbase Hrole Hppl Hcore5 Hfxk K5w) as (Hbase5 & Hrole5).
    (* the value entry's bytes *)
    assert (HPP5 : RPgMem.rm_bytes rsegs (w_H W2) mem5 (e_pp (x_e rsegs cx)) (Layout.pp_bytes rec)).
    { apply (RPgMem.rm_bytes_kept rsegs (w_H W2) mem2); [exact HPP2|].
      intros x Hx. rewrite Hppl' in Hx. apply K5; unfold Layout.PP_SIZE in *; lia. }
    assert (HENT5 : RPgMem.rm_bytes rsegs (w_H W2) mem5
      (e_pp (x_e rsegs cx) + (Layout.OFF_ENT + Layout.ENT_SIZE * Z.of_nat (S m)))
      (Layout.ent_mem (nth (S m) (Model.ents rec) RPgScanF.rk_d))).
    { apply (RPgMem.rm_pp_ent rsegs (Model.buf rec) (Model.is_props rec) (Model.has_params rec)
        (Model.params_struct rec) (Model.ents rec) (Model.corrupt rec)
        (m2k_buf_max rec Hwf) Hnent (m2k_bodies_96 rec Hwf)); [exact HPP5 | lia]. }
    pose proof (RPgScanF.rk_ent_wf_nth rec (S m) Hwf ltac:(lia)) as Hwfv.
    pose proof Hwfv as (Htv & Hbv & Hsv).
    assert (HVT : val_mem rsegs (mrestrict (w_H W2) mem5)
      (e_pp (x_e rsegs cx) + 0x4014 + 104 * (Z.of_nat m + 1)) 4
      (Model.e_type (nth (S m) (Model.ents rec) RPgScanF.rk_d))).
    { pose proof (RPgMem.rm_bytes_field rsegs (w_H W2) mem5 _ _ 0%nat 4%nat _ HENT5
        (m2k_ent_type_slice _ Hwfv) ltac:(rewrite (m2k_ent_mem_len _ Hwfv); lia)) as HV.
      replace (e_pp (x_e rsegs cx) + (Layout.OFF_ENT + Layout.ENT_SIZE * Z.of_nat (S m)) + Z.of_nat 0)
        with (e_pp (x_e rsegs cx) + 0x4014 + 104 * (Z.of_nat m + 1)) in HV
        by (unfold Layout.OFF_ENT, Layout.ENT_SIZE; lia).
      exact HV. }
    assert (HVS : val_mem rsegs (mrestrict (w_H W2) mem5)
      (e_pp (x_e rsegs cx) + 0x4014 + 104 * (Z.of_nat m + 1) + 4) 4
      (Model.e_size (nth (S m) (Model.ents rec) RPgScanF.rk_d))).
    { pose proof (RPgMem.rm_bytes_field rsegs (w_H W2) mem5 _ _ 4%nat 4%nat _ HENT5
        (m2k_ent_size_slice _ Hwfv) ltac:(rewrite (m2k_ent_mem_len _ Hwfv); lia)) as HV.
      replace (e_pp (x_e rsegs cx) + (Layout.OFF_ENT + Layout.ENT_SIZE * Z.of_nat (S m)) + Z.of_nat 4)
        with (e_pp (x_e rsegs cx) + 0x4014 + 104 * (Z.of_nat m + 1) + 4) in HV
        by (unfold Layout.OFF_ENT, Layout.ENT_SIZE; lia).
      exact HV. }
    assert (HVB : val_mem rsegs (mrestrict (w_H W2) mem5)
      (e_pp (x_e rsegs cx) + 0x4014 + 104 * (Z.of_nat m + 1) + 8) 4
      (Cursor.rd32 (Model.e_body (nth (S m) (Model.ents rec) RPgScanF.rk_d)))).
    { pose proof (RPgMem.rm_bytes_field rsegs (w_H W2) mem5 _ _ 8%nat 4%nat _ HENT5
        (m2k_ent_word_slice _ Hwfv) ltac:(rewrite (m2k_ent_mem_len _ Hwfv); lia)) as HV.
      replace (e_pp (x_e rsegs cx) + (Layout.OFF_ENT + Layout.ENT_SIZE * Z.of_nat (S m)) + Z.of_nat 8)
        with (e_pp (x_e rsegs cx) + 0x4014 + 104 * (Z.of_nat m + 1) + 8) in HV
        by (unfold Layout.OFF_ENT, Layout.ENT_SIZE; lia).
      exact HV. }
    pose proof (proj1 Hcore5) as HJ5. pose proof HJ5 as (HAR5 & _).
    destruct (RPgMem.rm_blk_ra rsegs B ly2 S2 W2 mem5 md5 (e_pp (x_e rsegs cx)) Layout.PP_SIZE
      (e_pp (x_e rsegs cx) + 0x4014 + 104 * (Z.of_nat m + 1)) 16 HAR5 HppIn ltac:(lia)
      ltac:(rewrite Hreq; unfold Layout.PP_SIZE; lia)) as (HRA5 & _).
    (* the dispatch *)
    apply (HKV fx2 ly2 S2 W2 regs5 mem5 md5 rec (nth (S m) (Model.ents rec) RPgScanF.rk_d)
      (e_pp (x_e rsegs cx) + 0x4014 + 104 * (Z.of_nat m + 1))).
    * exact Hbase5.
    * exact Hrole5.
    * exact Hppl.
    * unfold rs_at_cx, rs_at, rs_L_chk. cbn [app].
      repeat apply Forall_cons; try apply Forall_nil; cbn [rl_at rl_xv fst snd].
      -- subst regs5. etransitivity;
         [exact (CS2 (8%bv : bv 5) ltac:(cbv [In]; left; reflexivity)) | exact P8].
      -- subst regs5. etransitivity;
         [exact (CS2 (9%bv : bv 5) ltac:(cbv [In]; right; left; reflexivity)) | exact P9].
      -- subst regs5. etransitivity;
         [exact (CS2 (19%bv : bv 5) ltac:(cbv [In]; repeat (first [left; reflexivity | right]))) | exact P19].
      -- subst regs5. etransitivity;
         [exact (CS2 (23%bv : bv 5) ltac:(cbv [In]; repeat (first [left; reflexivity | right]))) | exact P23].
      -- subst regs5. etransitivity;
         [exact (CS2 (18%bv : bv 5) ltac:(cbv [In]; repeat (first [left; reflexivity | right]))) | exact P18].
      -- subst regs5. etransitivity;
         [exact (CS2 (22%bv : bv 5) ltac:(cbv [In]; repeat (first [left; reflexivity | right]))) | exact P22].
      -- eapply (val_mem_kept rsegs (w_H W2) (w_H W2) mem2 mem5); [|exact C08].
         intros k Hk. change (Z.of_nat 8) with 8 in Hk. apply K5; lia.
      -- eapply (val_mem_kept rsegs (w_H W2) (w_H W2) mem2 mem5); [|exact C30].
         intros k Hk. change (Z.of_nat 8) with 8 in Hk. apply K5; lia.
      -- subst regs5. etransitivity;
         [exact (CS2 (24%bv : bv 5) ltac:(cbv [In]; repeat (first [left; reflexivity | right]))) | exact P24].
       -- subst regs5. etransitivity; [exact RA0|].
         rewrite (m2k_denot_a0 E3 21 27 (Z.of_nat m + 1) (e_pp (x_e rsegs cx) + 0x4014)
           E21b ltac:(lia) E27b ltac:(unfold Layout.PP_SIZE in *; lia)
           ltac:(unfold Layout.PP_SIZE in *; lia)).
         reflexivity.
      -- eapply (val_mem_kept rsegs (w_H W2) (w_H W2) mem2 mem5); [|exact C28].
         intros k Hk. change (Z.of_nat 8) with 8 in Hk. apply K5; lia.
      -- eapply (val_mem_kept rsegs (w_H W2) (w_H W2) mem2 mem5); [|exact C80].
         intros k Hk. change (Z.of_nat 8) with 8 in Hk. apply K5; lia.
    * exact Hwfv.
    * exact HVT.
    * exact HVS.
    * exact HVB.
    * exact HRA5.
    * unfold Layout.PP_SIZE in *. lia.
    * unfold Layout.PP_SIZE in *. lia.
    * destruct Happ as [Hl|Hr]; [left | right]; unfold kLowShadowBeg, kHighMemBeg;
      unfold Layout.PP_SIZE in *; lia.
    * exact (m2k_inv_match rec at0 m kb Hinv Ham ltac:(lia) Hnone Hkey Hkbrole).
    * exact (proj1 (proj2 (proj2 (proj2 Hrec)))).
    * exact (proj2 (proj2 (proj2 (proj2 Hrec)))).
  + (* ---------------- the key is NOT the role key: back to the scan's outer head ---------------- *)
    assert (Hkbne : kb <> Role.ROLE_KEY).
    { intros Hkb. apply Hne0. apply Hres. rewrite Hkb. reflexivity. }
    assert (Hvr : bv_unsigned (getr regs3 (10%bv : bv 5)) <> 0).
    { rewrite H10. unfold strcmp_res in Hne0 |- *.
      destruct (Z.eqb_spec c1 c2) as [Ec|Ec]; [exfalso; apply Hne0; reflexivity|].
      destruct (c1 <? c2); vm_compute; discriminate. }
    pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3b & _).
    pose proof (m2_entry (fx := fx2) 0x822d4 []
      [m2_frame 0 0x100 0 0 [YP09.mkChunk 0xd8 (CVal 8 (SOff 32 0)); YP09.mkChunk 0xe0 (CVal 8 (SOff 33 0));
                             YP09.mkChunk 0xe8 (CVal 8 (SOff 34 0)); YP09.mkChunk 0xf0 (CVal 8 (SOff 35 0));
                             YP09.mkChunk 0xf8 (CVal 8 (SOff 36 0))]]
      m2k_facts W2 regs3
      [w64 (e_pp (x_e rsegs cx) + 0x4018); w64 (e_pp (x_e rsegs cx) + 0x401c);
       w64 (e_pp (x_e rsegs cx) + 0x401c); w64 (e_pp (x_e rsegs cx) + 0x4014);
       w64 (Z.of_nat (length (Model.ents rec)))] mem3
      (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
    specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil];
      apply (m2_frame_ok _ W2 mem3 (e_R (x_e rsegs cx)) (x_STK rsegs cx) (x_sp0 rsegs cx) 0 0x100 0 0);
      [exact E9b | lia | lia | exact Hpres3b | intros Hcc; lia |];
      repeat apply Forall_cons; try apply Forall_nil;
      [ exact (CH 0%nat (e_pp (x_e rsegs cx) + 0x4018) 0xd8 ltac:(unfold Layout.PP_SIZE in *; lia)
          ltac:(reflexivity) HS31)
      | exact (CH 1%nat (e_pp (x_e rsegs cx) + 0x401c) 0xe0 ltac:(unfold Layout.PP_SIZE in *; lia)
          ltac:(reflexivity) HS30)
      | exact (CH 2%nat (e_pp (x_e rsegs cx) + 0x401c) 0xe8 ltac:(unfold Layout.PP_SIZE in *; lia)
          ltac:(reflexivity) HS29)
      | exact (CH 3%nat (e_pp (x_e rsegs cx) + 0x4014) 0xf0 ltac:(unfold Layout.PP_SIZE in *; lia)
          ltac:(reflexivity) HS27)
      | exact (CH 4%nat (Z.of_nat (length (Model.ents rec))) 0xf8 ltac:(lia)
          ltac:(reflexivity) HS7) ])
      ltac:(cbn; tauto)
      ltac:(apply (m2k_facts_ok _ (e_R (x_e rsegs cx)) E9b ltac:(lia) HR16 E23b))).
    remember (Ereg regs3
      [w64 (e_pp (x_e rsegs cx) + 0x4018); w64 (e_pp (x_e rsegs cx) + 0x401c);
       w64 (e_pp (x_e rsegs cx) + 0x401c); w64 (e_pp (x_e rsegs cx) + 0x4014);
       w64 (Z.of_nat (length (Model.ents rec)))]) as E3 eqn:HE3.
    assert (HAE : env_agree 32 (Ereg regs3
      [w64 (e_pp (x_e rsegs cx) + 0x4018); w64 (e_pp (x_e rsegs cx) + 0x401c);
       w64 (e_pp (x_e rsegs cx) + 0x401c); w64 (e_pp (x_e rsegs cx) + 0x4014);
       w64 (Z.of_nat (length (Model.ents rec)))]) E3) by (subst E3; apply env_agree_refl).
    assert (SHOK : sh_ok rsegs M2_Bx [] E3 (mrestrict (w_H W2) mem3)) by constructor.
    assert (KE : forall a, 0 <= a < 2 ^ 64 ->
      ~ ((e_R (x_e rsegs cx) + 0xd8 <= a < e_R (x_e rsegs cx) + 0x100) \/
         (e_R (x_e rsegs cx) + 0x118 <= a < e_R (x_e rsegs cx) + 0x120) \/
         (e_R (x_e rsegs cx) - 16384 <= a < e_R (x_e rsegs cx))) ->
      aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem3 a) by (intros; reflexivity).
    pose proof HJ3 as HJ.
    change (w64 0x822d4) with (Z_to_bv 64 0x822d4).
    m2_run m2_awr. ck_keep m2k_kwr_ro.
    assert (E10b : ew E3 10 = Z_to_bv 64 (bv_unsigned (getr regs3 (10%bv : bv 5))))
      by (subst E3; rewrite (ew_Ereg_nat regs3 _ 10 (10%bv : bv 5) eq_refl), Z_to_bv_bv_unsigned;
          reflexivity).
    m2_branch Hb2.
    * (* taken: the scan goes on at m + 2 *)
      clear Hb2.
      m2_run m2_awr. ck_keep m2k_kwr_ro.
      lazymatch goal with HS : st_ok _ ?EE ?ss (restrict ?HH ?mm), HAE : env_agree 32 _ ?EE |- _ =>
        pose proof (cs_eq_of_st_ok _ _ ss mm regs3 _ [2; 3; 4]%bv HS HAE
          ltac:(vm_compute; reflexivity)) as C234b;
        pose proof (cs_eq_of_st_ok _ _ ss mm regs3 _ [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv HS HAE
          ltac:(vm_compute; reflexivity)) as CS2
      end.
      let R := fresh "Q1" in rreg HS (1%bv : bv 5) R.
      let R := fresh "Q7" in rreg HS (7%bv : bv 5) R.
      let R := fresh "Q11" in rreg HS (11%bv : bv 5) R.
      let R := fresh "Q14" in rreg HS (14%bv : bv 5) R.
      let R := fresh "Q27" in rreg HS (27%bv : bv 5) R.
      let R := fresh "Q28" in rreg HS (28%bv : bv 5) R.
      let R := fresh "Q29" in rreg HS (29%bv : bv 5) R.
      let R := fresh "Q30" in rreg HS (30%bv : bv 5) R.
      let R := fresh "Q31" in rreg HS (31%bv : bv 5) R.
      lazymatch goal with HS : st_ok _ ?EE ?ss (restrict ?HH ?mm) |- _ =>
        rewrite (st_ok_restrict_mkst rsegs HH EE ss mm HS eq_refl);
        replace (ss_pc ss) with RS_O by (vm_compute; reflexivity)
      end.
      lazymatch goal with HS : st_ok _ _ _ (restrict _ ?mm) |- _ =>
        remember (ms_mem mm) as mem5 eqn:Hmem5; remember (ms_regs mm) as regs5 eqn:Hregs5
      end.
      lazymatch goal with |- SRr _ _ (mkCfg _ ?md) _ => remember md as md5 eqn:Hmd5 end.
      assert (K5 : forall a, 0 <= a < 2 ^ 64 ->
        ~ ((e_R (x_e rsegs cx) + 0xd8 <= a < e_R (x_e rsegs cx) + 0x100) \/
           (e_R (x_e rsegs cx) + 0x118 <= a < e_R (x_e rsegs cx) + 0x120) \/
           (e_R (x_e rsegs cx) - 16384 <= a < e_R (x_e rsegs cx))) ->
        aview rsegs (w_H W2) mem5 a = aview rsegs (w_H W2) mem2 a).
      { intros a Ha Hz. rewrite (KE a Ha Hz). exact (K3 a Ha Hz). }
      assert (K5w : forall a, ~ m2k_wz cx a -> aview rsegs (w_H W2) mem5 a = aview rsegs (w_H W2) mem2 a).
      { intros a Hz. apply K5; unfold m2k_wz, T_SEG_STK, ASTACK in Hz; lia. }
      assert (Hcore5 : rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs5 mem5 md5).
      { apply (m2_core_step B MT MTL cx (rs_E2 rsegs cx) ly2 S2 W2 regs3 mem3 md3 ly2 S2 W2 regs5 mem5 md5
          Hcore3 ltac:(subst mem5 md5; exact HJ));
        [ intros r Hr; subst regs5; exact (C234b (Z_to_bv 5 r)
            ltac:(destruct Hr as [-> | [-> | ->] ]; cbv [In];
                  repeat (first [left; apply bv_eq; reflexivity | right])))
        | reflexivity | apply Permutation_refl | rewrite Hmd5; kio | apply (mo_le_refl MT MTL) |].
        intros a Ha Hs He. apply KE; [exact Ha|].
        intros [Hz|[Hz|Hz]].
        - apply He. unfold rs_E2. left. unfold rl_inw. cbn [hi_w2 role_himg_A].
          rewrite !Exists_cons, Exists_nil. cbn [rl_xv fst snd]. lia.
        - apply He. unfold rs_E2. left. unfold rl_inw. cbn [hi_w2 role_himg_A].
          rewrite !Exists_cons, Exists_nil. cbn [rl_xv fst snd]. lia.
        - apply Hs. rewrite HspR. unfold T_SEG_STK, ASTACK. lia. }
      destruct (m2k_chk_kept B MT LAWS cx rec fx2 fx2 ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 regs5 mem5 md5
        Hpre Hbase Hrole Hppl Hcore5 Hfxk K5w) as (Hbase5 & Hrole5).
      apply (HO fx2 ly2 S2 W2 regs5 mem5 md5 rec).
      split; [exact Hbase5|]. split.
      -- unfold rs_at_cx, rs_at, rs_L_scan, rs_L_chk. cbn [app].
         repeat apply Forall_cons; try apply Forall_nil; cbn [rl_at rl_xv fst snd].
         ++ subst regs5. etransitivity;
            [exact (CS2 (8%bv : bv 5) ltac:(cbv [In]; repeat (first [left; reflexivity | right]))) | exact P8].
         ++ subst regs5. etransitivity;
            [exact (CS2 (9%bv : bv 5) ltac:(cbv [In]; repeat (first [left; reflexivity | right]))) | exact P9].
         ++ subst regs5. etransitivity;
            [exact (CS2 (19%bv : bv 5) ltac:(cbv [In]; repeat (first [left; reflexivity | right]))) | exact P19].
         ++ subst regs5. etransitivity;
            [exact (CS2 (23%bv : bv 5) ltac:(cbv [In]; repeat (first [left; reflexivity | right]))) | exact P23].
         ++ subst regs5. etransitivity;
            [exact (CS2 (18%bv : bv 5) ltac:(cbv [In]; repeat (first [left; reflexivity | right]))) | exact P18].
         ++ subst regs5. etransitivity;
            [exact (CS2 (22%bv : bv 5) ltac:(cbv [In]; repeat (first [left; reflexivity | right]))) | exact P22].
         ++ eapply (val_mem_kept rsegs (w_H W2) (w_H W2) mem2 mem5); [|exact C08].
            intros k Hk. change (Z.of_nat 8) with 8 in Hk. apply K5; lia.
         ++ eapply (val_mem_kept rsegs (w_H W2) (w_H W2) mem2 mem5); [|exact C30].
            intros k Hk. change (Z.of_nat 8) with 8 in Hk. apply K5; lia.
         ++ subst regs5. etransitivity;
            [exact (CS2 (24%bv : bv 5) ltac:(cbv [In]; repeat (first [left; reflexivity | right]))) | exact P24].
          ++ subst regs5. etransitivity; [exact Q1|]. apply bv_eq. vm_compute. reflexivity.
         ++ subst regs5. etransitivity;
            [exact (CS2 (26%bv : bv 5) ltac:(cbv [In]; repeat (first [left; reflexivity | right]))) | exact P26].
          ++ subst regs5. etransitivity; [exact Q7|]. rewrite HE3.
             change 36%nat with (32 + 4)%nat. rewrite ew_Ereg_extra. cbn [nth]. reflexivity.
         ++ subst regs5. etransitivity;
            [exact (CS2 (20%bv : bv 5) ltac:(cbv [In]; repeat (first [left; reflexivity | right]))) | exact P20].
          ++ subst regs5. etransitivity; [exact Q28|]. rewrite HE3.
             rewrite (ew_Ereg_nat regs3 _ 27 (27%bv : bv 5) eq_refl). exact P27.
          ++ subst regs5. etransitivity; [exact Q27|]. rewrite HE3.
             change 35%nat with (32 + 3)%nat. rewrite ew_Ereg_extra. cbn [nth]. reflexivity.
          ++ subst regs5. etransitivity; [exact Q31|]. rewrite HE3.
             change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. cbn [nth]. reflexivity.
          ++ subst regs5. etransitivity; [exact Q29|]. rewrite HE3.
             change 34%nat with (32 + 2)%nat. rewrite ew_Ereg_extra. cbn [nth]. reflexivity.
          ++ subst regs5. etransitivity; [exact Q30|]. rewrite HE3.
             change 33%nat with (32 + 1)%nat. rewrite ew_Ereg_extra. cbn [nth]. reflexivity.
         ++ eapply (val_mem_kept rsegs (w_H W2) (w_H W2) mem2 mem5); [|exact C28].
            intros k Hk. change (Z.of_nat 8) with 8 in Hk. apply K5; lia.
         ++ eapply (val_mem_kept rsegs (w_H W2) (w_H W2) mem2 mem5); [|exact C80].
            intros k Hk. change (Z.of_nat 8) with 8 in Hk. apply K5; lia.
          ++ subst regs5. etransitivity; [exact Q11|]. rewrite HE3.
             rewrite (ew_Ereg_nat regs3 _ 25 (25%bv : bv 5) eq_refl).
             etransitivity; [exact P25|]. unfold w64. f_equal. lia.
         ++ subst regs5. exact Q14.
      -- split; [exact Hrole5|]. split; [|exact Hrec].
         exact (m2k_inv_mismatch rec at0 m kb Hinv Ham ltac:(lia) Hnone Hkey Hkbne).
    * (* not taken: a0 = 0 is the match, against strcmp_res c1 c2 <> 0 *)
      exfalso. rewrite branch_ne_U in Hb2.
      rewrite (m2k_U_atom E3 10 (bv_unsigned (getr regs3 (10%bv : bv 5))) E10b
        (word_range (getr regs3 (10%bv : bv 5)))) in Hb2.
      rewrite U_lit in Hb2 by lia.
      apply Bool.negb_false_iff, Z.eqb_eq in Hb2. exact (Hvr Hb2).
Qed.
End kc.

Print Assumptions rl_m02_key_cmp.
