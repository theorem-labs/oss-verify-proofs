(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Agree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2 ScanInt ScanCount RespLine.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require F_shgetc_A F_shgetc_B H_presp_A H_presp_B.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0 AllocA0 ATacAp.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import HttpAllocA HttpRepA AWKit AWAuto AWAuto2 FakeKit HObjK HObjF FsEnvKit H_scanner_get_token H_vfm_G H_match_A.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require HPrepA.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import AWUb2.
Import ListNotations.
Open Scope Z_scope.

Definition presp_entryA : Z := 0x87acc.
Notation FMT_SSCANF_A := 0x218e0%Z.
Notation ERRNO_A := 0x5e750c%Z.
Notation got_sspA := 0xab9c8%Z.
Notation ssp_guardA := 0x6075f0%Z.
Notation PRESP_DEPTH_A := 32768%Z.

Ltac split_chunk FR n H1 H2 :=
  lazymatch type of FR with rw_cells ?segs ?m ?A ?cs =>
    let cs1 := eval cbv beta iota delta [firstn skipn] in (firstn n cs) in
    let cs2 := eval cbv beta iota delta [firstn skipn] in (skipn n cs) in
    change (rw_cells segs m A (cs1 ++ cs2)) in FR;
    destruct (proj1 (rw_cells_app segs m A cs1 cs2) FR) as [H1 H2]; clear FR;
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in H2;
    try (lazymatch type of H2 with rw_cells _ _ (?a + ?b + ?c)%Z _ =>
           let v := eval vm_compute in (b + c)%Z in replace (a + b + c)%Z with (a + v)%Z in H2 by lia end)
  end.
Ltac recell FR i :=
  lazymatch type of FR with rw_cells ?segs ?m ?A ?cs =>
    let pre := eval cbv beta iota delta [firstn skipn] in (firstn i cs) in
    let post := eval cbv beta iota delta [firstn skipn] in (skipn (S i) cs) in
    lazymatch eval cbv beta iota delta [firstn skipn nth_error] in (nth_error cs i) with
    | Some (CB 8 ?b) => change (rw_cells segs m A (pre ++ CB 8 b :: post)) in FR; apply (rw_cells_CB_C8 segs m A pre b post) in FR; cbn [app] in FR
    | Some (CB 4 ?b) => change (rw_cells segs m A (pre ++ CB 4 b :: post)) in FR; apply (rw_cells_CB_C4 segs m A pre b post) in FR; cbn [app] in FR
    end end.
Ltac splitcb FR i sizes :=
  lazymatch type of FR with rw_cells ?segs ?m ?A ?cs =>
    let pre := eval cbv beta iota delta [firstn skipn] in (firstn i cs) in
    let post := eval cbv beta iota delta [firstn skipn] in (skipn (S i) cs) in
    lazymatch eval cbv beta iota delta [firstn skipn nth_error] in (nth_error cs i) with
    | Some (CB ?n ?b) => change (rw_cells segs m A (pre ++ CB n b :: post)) in FR;
        apply (rw_cells_split_CB segs m A pre n b post sizes) in FR; [| reflexivity]; cbn [app mk_CB_cells] in FR
    end end.
Ltac name_junk FR :=
  repeat lazymatch type of FR with context [CB _ (firstn ?a ?b)] => let j := fresh "jk" in remember (firstn a b) as j in FR
                      | context [CB _ (skipn ?a ?b)] => let j := fresh "jk" in remember (skipn a b) as j in FR end;
  repeat match goal with E : _ = firstn _ _ |- _ => clear E | E : _ = skipn _ _ |- _ => clear E end.

Ltac fk_move H FKc WMc :=
  lazymatch type of H with rw_cells _ ?m ?A2 ?cs2 =>
    lazymatch type of FKc with fkeep ?FIx ?Wc ?stx m ?m' =>
      apply (rw_cells_fkeep FIx Wc stx m m' A2 cs2) in H; [ | exact FKc | exact WMc | solve_in_live | dj_solve ] end end.

Ltac chk8N r APP HS :=
  let HA' := fresh "ACCn" in pose proof (proj1 HS) as HA'; acc_chk0 r APP HA'; clear HA'; step; clear_shr.

Ltac chkbN r APP HS k SHR Hk :=
  let a := reg_val r in
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (acc_load mm APP a (proj1 HS APP ltac:(lia)) ltac:(shadow_addr_tac)) as (k & SHR & Hk) end.

Ltac evalK K := repeat match type of K with
  | context [Z.land ?a ?b] => let v := eval vm_compute in (Z.land a b) in progress change (Z.land a b) with v in K
  | context [?a mod ?b] => let v := eval vm_compute in (a mod b) in progress change (a mod b) with v in K end.

Definition selw3 (i j k n : nat) (yi yj vk v : word) : word := if Nat.eqb n i then yi else if Nat.eqb n j then yj else if Nat.eqb n k then vk else v.
Ltac gen3v CONT pcnew i j k vk :=
  let v1 := reg_val 1 in let v2 := reg_val 2 in let v3 := reg_val 3 in let v4 := reg_val 4 in let v5 := reg_val 5 in let v6 := reg_val 6 in let v7 := reg_val 7 in let v8 := reg_val 8 in let v9 := reg_val 9 in let v10 := reg_val 10 in let v11 := reg_val 11 in let v12 := reg_val 12 in let v13 := reg_val 13 in let v14 := reg_val 14 in let v15 := reg_val 15 in let v16 := reg_val 16 in let v17 := reg_val 17 in let v18 := reg_val 18 in let v19 := reg_val 19 in let v20 := reg_val 20 in let v21 := reg_val 21 in let v22 := reg_val 22 in let v23 := reg_val 23 in let v24 := reg_val 24 in let v25 := reg_val 25 in let v26 := reg_val 26 in let v27 := reg_val 27 in let v28 := reg_val 28 in let v29 := reg_val 29 in let v30 := reg_val 30 in let v31 := reg_val 31 in
  lazymatch goal with |- evt ?sg ?P (MS _ ?F _ ?fc ?o ?mm ?ro) =>
    let T := constr:(forall yi yj : word, evt sg P (MS (mkR (selw3 i j k 1%nat yi yj vk v1) (selw3 i j k 2%nat yi yj vk v2) (selw3 i j k 3%nat yi yj vk v3) (selw3 i j k 4%nat yi yj vk v4) (selw3 i j k 5%nat yi yj vk v5) (selw3 i j k 6%nat yi yj vk v6) (selw3 i j k 7%nat yi yj vk v7) (selw3 i j k 8%nat yi yj vk v8) (selw3 i j k 9%nat yi yj vk v9) (selw3 i j k 10%nat yi yj vk v10) (selw3 i j k 11%nat yi yj vk v11) (selw3 i j k 12%nat yi yj vk v12) (selw3 i j k 13%nat yi yj vk v13) (selw3 i j k 14%nat yi yj vk v14) (selw3 i j k 15%nat yi yj vk v15) (selw3 i j k 16%nat yi yj vk v16) (selw3 i j k 17%nat yi yj vk v17) (selw3 i j k 18%nat yi yj vk v18) (selw3 i j k 19%nat yi yj vk v19) (selw3 i j k 20%nat yi yj vk v20) (selw3 i j k 21%nat yi yj vk v21) (selw3 i j k 22%nat yi yj vk v22) (selw3 i j k 23%nat yi yj vk v23) (selw3 i j k 24%nat yi yj vk v24) (selw3 i j k 25%nat yi yj vk v25) (selw3 i j k 26%nat yi yj vk v26) (selw3 i j k 27%nat yi yj vk v27) (selw3 i j k 28%nat yi yj vk v28) (selw3 i j k 29%nat yi yj vk v29) (selw3 i j k 30%nat yi yj vk v30) (selw3 i j k 31%nat yi yj vk v31)) F (Z_to_bv 64 pcnew) fc o mm ro)) in
    let T' := eval cbv beta iota delta [selw3 Nat.eqb] in T in
    assert (CONT : T') end.

Section W.
Context {HC : HasCeiling}.
Variable FI : fs_if.
Hypothesis IC : icpt_contracts.
Hypothesis STACK_MALLOC_0 : stack_malloc_stmt FI 0.
Hypothesis STACK_MALLOC_1 : stack_malloc_stmt FI 1.
Local Notation FSIV W := ((FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: W)%Z.

Variables (P A len cap lo q kq kP bn kE : Z) (bs sl : list byte) (st : fsstate FI).
Variables (rm isreq err hack pos entp clen csz esp SA slen scap : Z) (pad : word).
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (m0 : mem).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= q - PRESP_DEPTH_A.
Hypothesis AL16 : q = 16 * kq.
Hypothesis QHI : q < 2^64.
Hypothesis RF0 : RFAKE FI st m0.
Hypothesis FCO : fs_call_ok FI st tp 3.
Hypothesis FE0 : FSENV FI m0.

Let F := fs_F FI st 0.  Let FL := fs_FL FI st 0.  Let st1 := fs_next FI st 0.  Let SF := sh F.

Notation WP := [(P + 224, P + 288); (P + 440, P + 452); (P + 488, P + 496); (A, A + bn); (0x5e750c, 0x5e7510)]%Z.
Notation W0 := ((lo, q) :: FSIV WP)%Z.

Definition minvB (mb : mem) (q' : Z) (m : mem) (tyw tw1 tw2 lb ll : word) : Prop :=
  (exists k', q' = 32 * k') /\ q + -176 <= q' <= q + -160
  /\ stk asegs m lo q'
  /\ (exists j24 j4, rw_cells asegs m q' [CB 24 j24; C8 (wz F); CB 4 j4])
  /\ rw_cells asegs m (q' + 36) [C4 tyw]
  /\ rw_cells asegs m (q' + 40) [C8 tw1; C8 tw2]
  /\ stk asegs m (q' + 56) (q + -104)
  /\ rw_cells asegs m (q + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
  /\ rw_cells asegs m F [C8 (wz 0x41b58ab3); C8 (wz 0x12e44); C8 (wz 0x87acc); C8 (wz q')]
  /\ rw_cells asegs m (F + 32) [C8 lb; C8 ll]
  /\ (exists j8, rw_cells asegs m (F + 48) [CB 8 j8; C8 (wz FL)])
  /\ rw_cells asegs m SF [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)]
  /\ rw_cells asegs m FL [C1 (Z_to_bv 8 1)]
  /\ mem_inv asegs m
  /\ munch W0 mb m /\ wmono asegs mb m
  /\ fkeep FI WP st mb m /\ asan_env asegs m
  /\ (exists stc, RFAKE FI stc m /\ fs_live FI stc = fs_newff FI st 0 :: fs_live FI st).

Definition minvP := minvB m0.

Ltac mv_tacP := try unfold minvP; unfold minvB; split; [eexists; eassumption|]; split; [assumption|];
  repeat (split; [first [eassumption | (eexists; eassumption) | (eexists; eexists; eassumption)] |]); eexists; split; eassumption.

Hypothesis BN : Z.of_nat (length bs) = bn.
Hypothesis LBS : bn >= len.
Hypothesis BNMAX : bn <= 2^26 + 16.
Hypothesis CAP : len <= cap.
Hypothesis AHI : A + cap + 1 < 2^63.
Hypothesis SHWPo : shw m0 P 504.
Hypothesis PLO : 0x609000 <= P.
Hypothesis PHI : P + 504 <= alloc_ceiling.
Hypothesis PAL : P = 8 * kP.
Hypothesis PLB : lb (fs_live FI st) P 504.
Hypothesis SHWA : 0 < len -> shw m0 A len.
Hypothesis ALO : 0 <= A.
Hypothesis AIMG : 0 < len -> 0x609000 <= A.
Hypothesis ABHI : A + bn <= alloc_ceiling.
Hypothesis AFS : A + bn <= FSB FI \/ FSB FI + A0_FS_SIZE <= A.

Definition ABANDd : Prop := A + bn <= 0x7fff7000 \/ 0x10007fff8000 <= A.
Hypothesis ABAND : ABANDd.
Hypothesis SL7 : Z.of_nat (length sl) <= 7.
Hypothesis SLHI : A + bn + Z.of_nat (length sl) <= alloc_ceiling.
Hypothesis SLAL : A + bn + Z.of_nat (length sl) = 8 * kE.
Hypothesis SHWSEP : shw m0 SEPTAB_A 20.
Hypothesis SHWFMT : shw m0 FMT_RESP_A 16.
Hypothesis SHZ : shz m0 (sh lo) (sh q).
Hypothesis SHR : shr m0 (sh lo - sh lo mod 8) (sh q + 8).
Hypothesis Q47 : q <= 2^47 - 64.

Definition rinvP (m : mem) (sc maj min : Z) : Prop :=
  rw_cells asegs m (P + 224) [C4 (wz rm); C4 (wz sc)]
  /\ rw_cells asegs m (P + 232) [C8 (wz SA); C8 (wz slen); C8 (wz scap); C8 (wz 5)]
  /\ rw_cells asegs m (P + 264) [C8 (wz 0); C4 (wz isreq); C4 (wz maj); C4 (wz min); C4 pad]
  /\ rw_cells asegs m (P + 440) [C4 (wz err); C4 (wz hack); C4 (wz pos); C4 (wz entp); C4 (wz clen); C4 (wz 0); C8 (wz csz); C8 (wz esp)]
  /\ (exists ev, rw_cells asegs m ERRNO_A [C4 ev]).
Ltac rv_tacP := unfold rinvP; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption| eexists; eassumption].

Definition pinvP (m : mem) (cur sc maj min : Z) : Prop :=
  rw_cells asegs m (P + 480) [C8 (wz (P + 400)); C8 (wz cur); C4 (wz 0)]
  /\ rw_cells asegs m (P + 400) [C8 (wz A); C8 (wz len); C8 (wz cap); C8 (wz 5)]
  /\ rw_cells asegs m A [CB (Z.to_nat bn) bs]
  /\ bytes_at asegs m (A + bn) sl
  /\ rinvP m sc maj min.
Ltac pv_tacP := unfold pinvP; split; [eassumption|]; split; [eassumption|]; split; [assumption|]; split; [assumption| rv_tacP].
#[using="Type"] Lemma text_bytes : forall m, rw_cells asegs m A [CB (Z.to_nat bn) bs] -> bytes_at asegs m A bs.
Proof. intros m [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. Qed.

#[using="lo bs sl m0 RF0 PLB"] Lemma geomP : exists kF kB,
  F = 64 * kF /\ SF = 8 * kF + 2147450880 /\ FSB FI = 4096 * kB /\ sh (FSB FI) = 512 * kB + 2147450880
  /\ FSB FI + 36864 <= F /\ F + 64 <= FSB FI + 11571200 /\ FSB FI + 4096 <= FL /\ FL + 1 <= FSB FI + 36864
  /\ (P + 504 <= F \/ F + 64 <= P) /\ FSB FI + 36864 <= P /\ P + 504 <= FSB FI + 11571200
  /\ 6328320 <= FSB FI /\ FSB FI + 11571200 <= alloc_ceiling
  /\ (FSB FI + 11571200 <= 2147446784 \/ 17594333495296 <= FSB FI).
Proof.
  destruct (new_frame_facts FI st 0 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & FLO & FHI & FAL & FLLO & FLHI & APART).
  cbn [FB_of SB_of] in FHI.
  pose proof (lb_apart_new FI st 0 m0 F SF FL P 504 RF0 ltac:(lia) eq_refl eq_refl eq_refl PLB) as PFAP. cbn [FB_of] in PFAP.
  destruct PLB as (g & Hg & G1 & G2). pose proof (live_wf FI st m0 RF0) as LW. rewrite Forall_forall in LW.
  destruct (LW g Hg) as (KR & GLO & GHI & _). unfold ff_size in *.
  pose proof (fsb_ok FI) as (FSB1 & FSB2 & _ & FSB4 & FSB5).
  exists (F / 64), (FSB FI / 4096).
  split; [clear - FAL; Z.div_mod_to_equations; lia|].
  split; [unfold SF, sh, SHADOW_OFF; clear - FAL; Z.div_mod_to_equations; lia|].
  split; [clear - FSB4; Z.div_mod_to_equations; lia|].
  split; [unfold sh, SHADOW_OFF; clear - FSB4; Z.div_mod_to_equations; lia|].
  repeat (split; [first [assumption | lia]|]). first [assumption | lia].
Qed.

Notation LSTP pc q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 mm :=
  (MS (mkR x1 (Z_to_bv 64 q') gp tp x5 x6 x7 (Z_to_bv 64 q) (Z_to_bv 64 q') x10 x11 x12 x13 x14 x15 x16 x17
           (Z_to_bv 64 F) (Z_to_bv 64 P) (Z_to_bv 64 (F + 32)) x21 x22 x23 (Z_to_bv 64 F) (Z_to_bv 64 SF) (Z_to_bv 64 2147450880)
           x27 x28 x29 x30 x31)
      F_ (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

#[using="STACK_MALLOC_0 kq kP bs sl CLO LO AL16 QHI RF0 FCO FE0 st1 BN PLO PHI PAL PLB ABHI AFS SLHI Q47"] Lemma prologueP : forall t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
  stk asegs m0 lo q -> mem_inv asegs m0 -> asan_env asegs m0 ->
  forall (Q : machine_state -> Prop),
  (forall q' m tyw tw1 tw2 lb ll x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31, minvP q' m tyw tw1 tw2 lb ll ->
     munch ((lo, q) :: FSIV []) m0 m -> fkeep FI [] st m0 m ->
     evt asegs Q (LSTP 0x87bf4 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (P + 480)) (Z_to_bv 64 4) (Z_to_bv 64 2) s11 x28 x29 x30 x31 m)) ->
  evt asegs Q
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (Z_to_bv 64 presp_entryA) fc None m0 (seg_rom asegs)).
Proof.
  intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ST MI AG Q K. unfold presp_entryA.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof AG as AE. apply asan_env_globals in AG. ag_split AG.
  pose proof geomP as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  destruct (new_frame_facts FI st 0 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & _ & _ & _ & _ & _ & APART).
  cbn [FB_of SB_of] in APART.
  pose proof (new_frame_fk FI st 0 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
  pose proof (munch_refl W0 m0) as MU. pose proof (wmono_refl asegs m0) as WM.
  pose proof (munch_refl ((lo, q) :: FSIV [])%Z m0) as MUP.
  pose proof (munch_refl [(lo, q)]%Z m0) as MU0. pose proof (wmono_refl asegs m0) as WM0.
  pose proof (fkeep_refl FI [] st m0) as FK. assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI st)) by (intros g Hg; exact Hg).
  pose proof RF0 as RF.
  carve_frame 160%nat ST.
  step. do 14 (step; fix_lit_store).
  step.
  step.
  rewrite (unsigned_lit (q + -160)) by lia. rewrite land_align32 by lia.
  remember (q + -160 - (q + -160) mod 32)%Z as q' eqn:Eq0.
  assert (Hq : q' = q + -160 \/ q' = q + -160 - 16) by (subst q'; apply align32_cases; clear - AL16; Z.div_mod_to_equations; lia).
  assert (Hq32 : exists k', q' = 32 * k') by (exists ((q + -160) / 32); clear - Eq0; Z.div_mod_to_equations; lia).
  assert (QL : q + -176 <= q' <= q + -160) by (clear - Hq; lia).
  clear Eq0.
  lazymatch goal with FRx : rw_cells asegs ?mm (q + -160) (?c0 :: ?c1 :: ?rest) |- _ =>
    destruct (align_frame_gen mm lo (q + -160) q' [c0; c1] rest 56%nat ST ltac:(lia) FRx eq_refl ltac:(lia) Hq) as (STq & (jq & QC) & GAP & FRhi);
    clear FRx end.
  clear Hq.
  clear ST. rename STq into ST. change (Z.of_nat 56) with 56 in GAP, FRhi. replace (q + -160 + 56) with (q + -104) in GAP, FRhi by lia.
  step.
  step. step. step. step.
  step. step.
  step.
  step.   lit_branch.
  step.
  step.
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  pose proof (fs_call_ok_le FI _ _ _ 1%nat FCO ltac:(lia)) as FCO1.
  call (STACK_MALLOC_0 st lo q' 64 F SF FL 64 24%nat 8%nat).
  all: side (try (first [ assumption | reflexivity | (unfold A0_RT_STACK in *; lia) ])).
  match goal with A : asan_env asegs _ |- _ => try clear AE; rename A into AE end.
  match goal with R : RFAKE FI (fs_next FI st 0) _ |- _ => rename R into RF end.
  match goal with E : fs_live FI _ = _ :: _ |- _ => rename E into LIVE1 end. fold st1 in LIVE1, RF.
  match goal with K0 : fkeep FI [] st _ _ |- _ => rename K0 into FKc end.
  match goal with P : rw_cells asegs _ F _ |- _ => rename P into FRF end.
  match goal with P : rw_cells asegs _ SF _ |- _ => rename P into SHF; shadow_cells_lit SHF end.
  match goal with P : rw_cells asegs _ FL _ |- _ => rename P into FLG end.
  fs_after_call FI FK FKc LSUB LIVE1 [(lo, q); (F, F + 64); (SF, SF + 8)]%Z.
  pose proof (lb_new _ _ _ LIVE1) as LVF. pose proof (ls_new _ _ _ LIVE1) as LVS. pose proof (lf_new _ _ _ LIVE1) as LVL.
  unfold ff_size, ff_shsize in LVF, LVS. rewrite FCLS in LVF, LVS. cbn [FB_of SB_of] in LVF, LVS.
  change (ff_addr (fs_newff FI st 0)) with F in LVF, LVS. change (ff_flag (fs_newff FI st 0)) with FL in LVL. change (sh F) with SF in LVS.
  step. step.
  step.   if_cases K0; zify_cond K0. 2:{ exfalso. lia. } clear K0.
  step; fix_lit_store.
  do 8 step.
  step; fix_lit_store. step; fix_lit_store. step; fix_lit_store.
  step. step.
  replace (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 F)) 3 + 2147450880)) with (Z_to_bv 64 SF)
    by (f_equal; rewrite unsigned_lit by lia; rewrite shiftr3_div; reflexivity).
  sstep. sstep.
  sstep. sstep.
  step.
  do 4 sstep.
  step. ubr.
  zstep. step. ubr.
  step.
  step; fix_lit_store. step; fix_lit_store.
  step. step. step.

  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  splitcb QC 2%nat [4; 4; 8; 8]%nat. recell QC 3%nat. recell QC 4%nat. recell QC 5%nat. name_junk QC.
  split_chunk QC 3%nat Q0 R0. split_chunk R0 1%nat TYC TC.
  replace (q' + 36 + 4) with (q' + 40) in TC by lia.
  splitcb FRF 4%nat [8; 8; 8]%nat. recell FRF 4%nat. recell FRF 5%nat. name_junk FRF.
  split_chunk FRF 4%nat FH R1. split_chunk R1 2%nat LINE FT.
  replace (F + 32 + 16) with (F + 48) in FT by lia.
  lazymatch type of FK with fkeep _ _ _ _ ?mm => assert (FKW : fkeep FI WP st m0 mm) by (eapply fkeep_weaken; [exact FK| intros a Ha; exact I| intros g Hg; exact Hg]) end.
  destruct Hq32 as (kq' & Hq32).
  eapply K; [mv_tacP| exact MUP| exact FK].
Qed.

#[using="HC FI lo bs sl st m0 F FL SF SHWPo ALO ABAND"] Lemma WP_app : app_ivs WP.
Proof.
  pose proof (shw_win_ok _ _ _ SHWPo) as WK. unfold app_ivs.
  do 3 (apply Forall_cons; [eapply app_iv_of_win_ok; [exact WK| lia| lia]|]).
  apply Forall_cons; [pose proof ABAND as ABu; unfold ABANDd in ABu; unfold app_iv, SH_HI; cbn [fst snd]; clear - ABu ALO LBS BN; lia|].
  apply Forall_cons; [apply app_iv_low; lia|]. apply Forall_nil.
Qed.
#[using="bs sl st m0 CLO F FL SF SHWPo ALO ABAND"] Lemma W0_fsw : Forall (fsw_iv FI) W0.
Proof. apply fsw_cons_app; [apply app_iv_stack; exact CLO| apply fsw_FSIV; exact WP_app]. Qed.
#[using="lo bs sl st m0 F FL SF SHWPo ALO ABAND"] Lemma WP_out : forall a, sh (FSB FI) <= a < sh (FSB FI) + A0_FS_SHSIZE -> outside WP a.
Proof.
  intros a Ha. apply (app_ivs_outside WP a WP_app).
  pose proof (fsb_ok FI) as FSBOK. destruct FSBOK as (F1 & F2 & F3 & F4 & F5).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  unfold shband, SH_LO, SH_HI. unfold sh, SHADOW_OFF in Ha. Z.div_mod_to_equations. lia.
Qed.

#[using="bs sl RF0 F FL SF SHWPo PLB ALO ABAND"] Lemma shwP_now : forall m X n, munch W0 m0 m -> fkeep FI WP st m0 m -> P <= X -> X + n <= P + 504 -> 0 <= n -> shw m X n.
Proof.
  intros m X n MU FK H1 H2 H3.
  eapply (shw_fkeep FI WP st m0 m X n); [eapply shw_sub; [exact SHWPo| lia| lia| lia]| exact FK| exact RF0| eapply lb_sub; [exact PLB| lia| lia]| exact WP_out].
Qed.

#[using="kq bs sl st CLO AL16 F FL SF SHWPo ALO ABAND SHZ Q47"] Lemma shwS_now : forall m X n, munch W0 m0 m -> lo + 64 <= X -> X + n + 64 <= q -> 0 <= n -> shw m X n.
Proof.
  intros m X n MU H1 H2 H3.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (shz_stack_fs FI W0 m0 m lo (sh lo) (sh q) SHZ CLO (stack_lo_ok lo) (sh_hi_ok q ltac:(clear - Q47; lia)) MU W0_fsw) as SHZm.
  apply (shw_of_shz m (sh lo) (sh q) X n SHZm).
  - unfold win_ok. split; [lia|]. right. lia.
  - unfold sh, SHADOW_OFF. Z.div_mod_to_equations. lia.
  - unfold sh, SHADOW_OFF. Z.div_mod_to_equations. lia.
Qed.

#[using="bs sl st CLO F FL SF SHWPo ALO ABAND SHZ Q47"] Lemma shzS_now : forall m, munch W0 m0 m -> shz m (sh lo) (sh q).
Proof.
  intros m MU. exact (shz_stack_fs FI W0 m0 m lo (sh lo) (sh q) SHZ CLO (stack_lo_ok lo) (sh_hi_ok q ltac:(clear - Q47; lia)) MU W0_fsw).
Qed.
#[using="bs sl st CLO F FL SF SHWPo ALO ABAND SHR Q47"] Lemma shrS_now : forall m, munch W0 m0 m -> shr m (sh lo - sh lo mod 8) (sh q + 8).
Proof.
  intros m MU. exact (shr_stack_fs FI W0 m0 m lo _ _ SHR CLO (Z.le_refl _) (sh_hi_ok8 q Q47) MU W0_fsw).
Qed.

#[using="kq bs sl st CLO LO AL16 F FL SF SHWPo ALO ABAND SHZ SHR Q47"] Lemma shwStk_now : forall m q', munch W0 m0 m -> q + -176 <= q' <= q + -160 -> shw m lo (q' - lo).
Proof.
  intros m q' MU Hq.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  apply (shw_of_shz_shr m (sh lo) (sh q) (sh lo - sh lo mod 8) (sh q + 8) lo (q' - lo) (shzS_now m MU) (shrS_now m MU)).
  - unfold win_ok. split; [lia|]. right. lia.
  - lia.
  - unfold sh, SHADOW_OFF. Z.div_mod_to_equations. lia.
  - lia.
  - unfold sh, SHADOW_OFF. Z.div_mod_to_equations. lia.
Qed.
#[using="bs sl st CLO F FL SF SHWPo ALO ABAND"] Lemma shwG_now : forall m X n, shw m0 X n -> munch W0 m0 m -> X + n <= 0x609000 -> shw m X n.
Proof.
  intros m X n H MU HX. apply (shw_frame_fs FI W0 m0 m X n H MU W0_fsw). left.
  pose proof (fsb_ok FI) as (B1 & _). lia.
Qed.
#[using="P lo bs sl m0 RF0 FL PLB"] Lemma shwL_now : forall m,
  rw_cells asegs m SF [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
                       C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)] ->
  shw m (F + 32) 16.
Proof.
  intros m SHF.
  destruct geomP as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (FAL : F mod 8 = 0) by (clear - EKF; Z.div_mod_to_equations; lia).
  change (rw_cells asegs m (sh F) (shadow_cells [241; 241; 241; 241; 0; 0; 243; 243])) in SHF.
  assert (S32 : sh (F + 32) = sh F + 4) by (unfold sh; clear - EKF; Z.div_mod_to_equations; lia).
  assert (S47 : sh (F + 32 + 16 - 1) = sh F + 5) by (unfold sh; clear - EKF; Z.div_mod_to_equations; lia).
  assert (SM : sh F mod 8 = 0) by (unfold sh, SHADOW_OFF; clear - EKF; Z.div_mod_to_equations; lia).
  split; [| split].
  - apply (accessible_of_chunk m F [241; 241; 241; 241; 0; 0; 243; 243] (F + 32) 16 SHF FAL); [lia| cbn [length]; lia|].
    intros i Hi H1 H2. cbn [length] in Hi.
    assert (i = 4%nat \/ i = 5%nat) as [-> | ->] by lia; reflexivity.
  - apply (sh_readable_of_chunk m F [241; 241; 241; 241; 0; 0; 243; 243] (F + 32) 16 SHF).
    + rewrite S32. clear - SM. Z.div_mod_to_equations. lia.
    + rewrite S47. cbn [length]. clear - SM. Z.div_mod_to_equations. lia.
  - unfold win_ok. split; [lia|]. clear - GF1 GF2 FSB1 FSB2 FSB5 ACR. lia.
Qed.

#[using="lo bs sl m0 RF0 PLB"] Lemma liveP : forall stc, fs_live FI stc = fs_newff FI st 0 :: fs_live FI st ->
  lb (fs_live FI stc) F 64 /\ ls (fs_live FI stc) SF 8 /\ lf (fs_live FI stc) FL /\ lb (fs_live FI stc) P 504
  /\ (forall g, In g (fs_live FI st) -> In g (fs_live FI stc)).
Proof.
  intros stc LIVE1.
  destruct (new_frame_facts FI st 0 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & _).
  assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI stc)) by (intros g Hg; rewrite LIVE1; right; exact Hg).
  pose proof (lb_new _ _ _ LIVE1) as LVF. pose proof (ls_new _ _ _ LIVE1) as LVS. pose proof (lf_new _ _ _ LIVE1) as LVL.
  unfold ff_size, ff_shsize in LVF, LVS. rewrite FCLS in LVF, LVS. cbn [FB_of SB_of] in LVF, LVS.
  change (ff_addr (fs_newff FI st 0)) with F in LVF, LVS. change (ff_flag (fs_newff FI st 0)) with FL in LVL. change (sh F) with SF in LVS.
  split; [exact LVF|]. split; [exact LVS|]. split; [exact LVL|]. split; [exact (lb_mono _ _ _ _ PLB LSUB)| exact LSUB].
Qed.

#[using="lo bs sl st F FL SF"] Lemma fkeep_weaken_fk : forall W Wc sta stb m mx m',
  fkeep FI Wc stb m m' -> RFAKE FI sta mx -> (forall g, In g (fs_live FI sta) -> In g (fs_live FI stb)) ->
  Forall (fk_ok FI W sta) Wc -> fkeep FI W sta m m'.
Proof.
  intros W Wc sta stb m mx m' H HR HL OK a Ha (g & Hg & Hp) Ho.
  apply H; [exact Ha| exists g; split; [apply HL; exact Hg| exact Hp]|].
  apply outside_of_forall. eapply Forall_impl; [| exact OK]. intros [lo' hi'] K. unfold fk_ok, fst, snd in K. unfold fst, snd.
  destruct K as [K|[K|K]].
  - intros Hr. apply (inside_not_outside W lo' (hi' - lo') a K); [lia| exact Ho].
  - pose proof (live_pieces_inside FI sta mx g a HR Hg Hp) as X. lia.
  - rewrite Forall_forall in K. specialize (K g Hg). unfold fst, snd in K. unfold in_pieces in Hp. lia.
Qed.

Definition hid2 (X : Prop) : Prop := X.
#[using="Type"] Lemma W0_absorb : forall mb m m' Ws, munch W0 mb m -> munch Ws m m' -> sub_fp Ws W0 -> munch W0 mb m'.
Proof. intros mb m m' Ws MU MUs SUB. eapply (munch_trans W0 mb m m' MU). eapply (munch_weaken Ws W0 m m' SUB MUs). Qed.
#[using="bs sl st F FL SF"] Lemma sub_fp_text : forall a b, A <= a -> b <= A + bn -> sub_fp [(a, b)] W0.
Proof. intros a b H1 H2 x Hx. cbn [outside] in *. destruct Hx as (_ & _ & _ & _ & _ & _ & H7 & _). split; [lia| exact I]. Qed.
#[using="bs sl st F FL SF"] Lemma sub_fp_P : forall a b,
  ((P + 224 <= a /\ b <= P + 288) \/ (P + 440 <= a /\ b <= P + 452) \/ (P + 488 <= a /\ b <= P + 496)) -> sub_fp [(a, b)] W0.
Proof. intros a b H x Hx. cbn [outside] in *. destruct Hx as (_ & _ & _ & H4 & H5 & H6 & _). split; [lia| exact I]. Qed.
Ltac hideW0 MU WM := lazymatch type of MU with ?T => change (hid2 T) in MU end; lazymatch type of WM with ?T => change (hid2 T) in WM end.

Ltac absorbW0 MU WM MUs WMs SUB :=
  unfold hid2 in MU, WM;
  lazymatch type of MUs with munch ?Ws ?ma ?mf =>
  lazymatch type of MU with munch _ ?mb0 _ =>
    let MUn := fresh "MUn" in let WMn := fresh "WMn" in
    pose proof (W0_absorb mb0 ma mf Ws MU MUs SUB) as MUn; pose proof (wmono_trans asegs mb0 ma mf WM WMs) as WMn;
    clear MU WM; rename MUn into MU; rename WMn into WM end end.

#[using="IC kq kP kE CLO LO AL16 RF0 BN LBS CAP AHI SHWPo PLO PHI PAL PLB SHWA ALO AIMG ABHI AFS ABAND SL7 SLHI SLAL SHWSEP SHZ Q47"] Lemma tokloopP : forall (k : nat) (cur sc maj min : Z) q' m tyw tw1 tw2 lb ll x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 (Q : machine_state -> Prop),
  len - cur < Z.of_nat k -> 0 <= cur <= len -> minvP q' m tyw tw1 tw2 lb ll -> pinvP m cur sc maj min ->
  FSENV FI m ->
  (forall r cur' m' tyw' tw1' tw2' y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
     (r <> 4 /\ 0 <= r <= 5) -> cur <= cur' <= len -> minvP q' m' tyw' tw1' tw2' lb ll -> pinvP m' cur' sc maj min ->
     evt asegs Q (LSTP 0x88094 q' y1 y5 y6 y7 (Z_to_bv 64 r) y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (P + 480)) (Z_to_bv 64 4) (Z_to_bv 64 2) x27 y28 y29 y30 y31 m')) ->
  (forall cur1 tlz ty m' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
     cur <= cur1 -> 1 <= tlz -> cur1 + tlz <= len -> 0 <= ty <= 5 -> ty <> 1 -> ty <> 2 ->
     minvP q' m' (wz ty) (wz (A + cur1)) (wz tlz) lb ll -> pinvP m' (cur1 + tlz) sc maj min -> FSENV FI m' ->
     evt asegs Q (LSTP 0x87c14 q' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (P + 480)) (Z_to_bv 64 4) (Z_to_bv 64 2) x27 y28 y29 y30 y31 m')) ->
  evt asegs Q (LSTP 0x87bf4 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (P + 480)) (Z_to_bv 64 4) (Z_to_bv 64 2) x27 x28 x29 x30 x31 m).
Proof.
  induction k as [|k IH]; intros until Q; intros HK HCUR INV PINV FE KEXIT KTOK; [lia|].
  destruct INV as ((kq' & Hq32) & Hq & ST & (j24 & j4 & QC) & TYC & TC & GAP & FRhi & FH & LINE & (j8 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (SC & MBC & TXC & SLK & (RSC & SMC & VERC & CTLC & (ev & ERRC))). pose proof (text_bytes _ TXC) as BUF.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
  zstep. zstep. zstep. step.

  pose proof geomP as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  destruct (liveP stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  eapply evt_cut.
  { eapply (scanner_get_token_spec_A IC) with (S := P + 480) (T := q' + 40) (TY := q' + 36) (MB := P + 400) (A := A) (cur := cur) (len := len) (cap := cap) (lo := lo) (bs := bs) (q := q');
    [ exact SC | exact MBC | exact BUF | (rewrite BN; exact LBS) | exact HCUR | exact CAP | exact AHI | exact TC | exact TYC | exact AE
    | apply (shwP_now m (P + 480) 24 MU FK); lia | apply (shwP_now m (P + 400) 32 MU FK); lia
    | apply (shwS_now m (q' + 40) 16 MU); lia | apply (shwS_now m (q' + 36) 4 MU); lia
    | intros HL; apply (shw_frame_fs FI W0 m0 m A len (SHWA HL) MU W0_fsw); clear - AFS LBS BN; lia
    | apply (shw_frame_fs FI W0 m0 m SEPTAB_A 20 SHWSEP MU W0_fsw); left; unfold SEPTAB_A; lia
    | lia | lia | clear - PAL; Z.div_mod_to_equations; lia | lia | lia | clear - PAL; Z.div_mod_to_equations; lia
    | lia | left; lia | (clear - Hq32; Z.div_mod_to_equations; lia) | lia | lia | (clear - Hq32; Z.div_mod_to_equations; lia) | exact ALO | (rewrite BN; exact ABHI) | (intros HL; pose proof (AIMG HL); lia) | lia | right; lia
    | right; lia | right; clear - ABHI CLO LO Hq BN; lia
    | clear - AFS PFS1 PFS2 LBS BN; lia | exact ST | exact CLO | lia | unfold A0_RT_STACK; lia | exact MI | reflexivity | reflexivity | reflexivity ]. }
  intros ms' PO. unfold sgt_post_A in PO.
  destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & r & cur' & tb & tl & tyw' & -> & MUc & WMc & MI' & ST' & AE' & SC' & TC' & TYC' & RES).
  pose proof MUc as MUt. pose proof WMc as WMt.

  fs_sync FI RF MUc WMc FK LSUB.

  clear SC TC TYC ST AE MI.
  clear BUF.
  transport_after_call asegs m m' MUt WMt. clear MUt WMt.
  replace (ret_pc (Z_to_bv 64 556036)) with (Z_to_bv 64 556036) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

  replace (ret_pc (Z_to_bv 64 556036)) with (Z_to_bv 64 556036) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  assert (RR : r = 4 \/ r <> 4) by lia.
  destruct RR as [R4 | RN4].

  -
    destruct RES as [(tlz & ty & _ & -> & -> & -> & TL1 & -> & TL2 & TYR & STRICT & _ & _) | ([X|X] & _ & _)]; [| unfold PARSE_INCOMPLETE in X; lia | unfold PARSE_FAILURE in X; lia].
    subst r.
    assert (MVN : minvP q' m' (wz ty) (wz (A + cur)) (wz tlz) lb ll).
    { mv_tacP. }
    assert (PVN : pinvP m' (cur + tlz) sc maj min) by pv_tacP.
    step. lit_branch.
    step. rewrite (sx32_lit ty) by lia. zstep. step. if_cases K2; zify_cond K2; rewrite swrap32_id in K2 by lia.
    +
      assert (TY12 : ty = 1 \/ ty = 2) by (clear - K2 TYR; assert (C : ty = 0 \/ ty = 1 \/ ty = 2 \/ ty = 3 \/ ty = 4 \/ ty = 5) by lia; destruct C as [->|[->|[->|[->|[->| ->]]]]]; evalK K2; lia).
      apply (IH (cur + tlz) sc maj min) with (tyw := wz ty) (tw1 := wz (A + cur)) (tw2 := wz tlz) (lb := lb) (ll := ll); [lia| lia| exact MVN| exact PVN| exact FE| |].
      * intros r0 cur'0 m'0 tyw'0 tw1'0 tw2'0 z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 RN CR MV0 PV0. apply (KEXIT r0 cur'0 m'0 tyw'0 tw1'0 tw2'0); [exact RN| lia| exact MV0| exact PV0].
      * intros cur1 tlz1 ty1 m'1 z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 C1 T1 T2 T3 T4 T5 MV1 PV1 FE1. apply (KTOK cur1 tlz1 ty1 m'1); try assumption. lia.
    +
      assert (TYN : ty <> 1 /\ ty <> 2) by (clear - K2 TYR; assert (C : ty = 0 \/ ty = 1 \/ ty = 2 \/ ty = 3 \/ ty = 4 \/ ty = 5) by lia; destruct C as [->|[->|[->|[->|[->| ->]]]]]; evalK K2; lia).
      apply (KTOK cur tlz ty m'); [lia| lia| lia| lia| lia| lia| exact MVN| exact PVN| exact FE].
  -
    destruct RES as [(tlz & ty & X & _) | (RR & -> & ->)]; [unfold PARSE_OK in X; lia|].
    assert (MVN : minvP q' m' tyw tb tl lb ll).
    { mv_tacP. }
    assert (PVN : pinvP m' cur sc maj min) by pv_tacP.
    unfold PARSE_INCOMPLETE, PARSE_FAILURE in RR.
    step. if_cases K1; zify_cond K1. 2:{ exfalso. destruct RR as [-> | ->]; revert K1; rewrite ?unsigned_lit by lia; lia. }
    apply (KEXIT r cur m' tyw tb tl); [lia| lia| exact MVN| exact PVN].
Qed.

#[using="IC STACK_MALLOC_0 STACK_MALLOC_1 kq kP kE CLO LO AL16 RF0 FCO BN LBS BNMAX CAP AHI SHWPo PLO PHI PAL PLB SHWA ALO AIMG ABHI AFS ABAND SL7 SLHI SLAL SHWSEP SHWFMT SHZ SHR Q47"] Lemma pbmatchP : forall (cur1 tlz ty sc maj min : Z) q' m lb ll x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 (Q : machine_state -> Prop),
  0 <= cur1 -> 1 <= tlz -> cur1 + tlz <= len ->
  minvP q' m (wz ty) (wz (A + cur1)) (wz tlz) lb ll -> pinvP m (cur1 + tlz) sc maj min ->
  FSENV FI m ->
  (forall r cur' m' tyw' tw1' tw2' lb' ll' y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
     (r <> 4 /\ 0 <= r <= 5) -> cur1 <= cur' <= len -> minvP q' m' tyw' tw1' tw2' lb' ll' -> pinvP m' cur' sc maj min ->
     evt asegs Q (LSTP 0x88094 q' y1 y5 y6 y7 (Z_to_bv 64 r) y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (P + 480)) (Z_to_bv 64 4) (Z_to_bv 64 2) x27 y28 y29 y30 y31 m')) ->
  (forall cur' o l m' tyw' tw1' tw2' y1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
     cur1 <= o -> 0 <= l -> o + l < cur' -> cur' <= len ->
     (exists b, nth_error bs (Z.to_nat (o + l)) = Some b /\ (bv_unsigned b = 13 \/ bv_unsigned b = 10)) ->
     minvP q' m' tyw' tw1' tw2' (wz (A + o)) (wz l) -> pinvP m' cur' sc maj min ->
     evt asegs Q (LSTP 0x87c54 q' y1 y5 y6 y7 (Z_to_bv 64 4) (Z_to_bv 64 4) y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (P + 480)) (Z_to_bv 64 4) (Z_to_bv 64 2) x27 y28 y29 y30 y31 m')) ->
  evt asegs Q (LSTP 0x87c14 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (P + 480)) (Z_to_bv 64 4) (Z_to_bv 64 2) x27 x28 x29 x30 x31 m).
Proof.
  intros until Q; intros HC1 HT1 HT2 INV PINV FE KEXIT KOK.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j24 & j4 & QC) & TYC & TC & GAP & FRhi & FH & LINE & (j8 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (SC & MBC & TXC & SLK & (RSC & SMC & VERC & CTLC & (ev & ERRC))). pose proof (text_bytes _ TXC) as BUF.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
  pose proof geomP as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  pose proof (munch_refl [(P + 488, P + 496)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  step. step. step.
  pose proof (proj1 (shwP_now m (P + 488) 8 MU FK ltac:(lia) ltac:(lia) ltac:(lia))) as ACC.
  acc_chk0 11 (P + 488) ACC. clear ACC.
  step. clear_shr.

  step. lit_branch.
  step. step. step.
  step; fix_lit_store.
  rewrite !unsigned_lit in SC by lia. replace (cur1 + tlz - tlz) with cur1 in SC by lia.
  step. step. step. step. step.
  destruct (liveP stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.

  eapply evt_cut.
  { eapply (match_respA IC FI STACK_MALLOC_0 STACK_MALLOC_1 (P + 480) (P + 400) A len cap cur1 (F + 32) lo q' bs stc lb ll);
    [ exact SC | exact MBC | exact BUF | exact LINE
    | exact CLO | lia | (clear - Hq32; Z.div_mod_to_equations; lia) | (clear - Q47 Hq; lia)
    | lia | lia | lia | (clear - PAL; Z.div_mod_to_equations; lia) | (clear - PAL; Z.div_mod_to_equations; lia)
    | apply (lb_sub _ P 504 _ _ PLB1); lia
    | exact ALO | (rewrite BN; exact ABHI) | (rewrite BN; exact LBS) | exact CAP | exact AHI | (intros HL; pose proof (AIMG HL); lia) | lia
    | (clear - AFS PFS1 PFS2 LBS BN; lia) | (rewrite BN; exact AFS) | (rewrite BN; exact ABAND)
    | (clear - EKF; Z.div_mod_to_equations; lia) | apply (lb_sub _ F 64 _ _ LVF); lia
    | (clear - PFAP; lia) | (clear - AFS GF1 GF2 LBS BN; lia)
    | apply (shwP_now _ (P + 480) 24 MU FK); lia | apply (shwP_now _ (P + 400) 32 MU FK); lia
    | intros HL; apply (shw_frame_fs FI W0 m0 _ A len (SHWA HL) MU W0_fsw); clear - AFS LBS BN; lia
    | apply (shwG_now _ SEPTAB_A 20 SHWSEP MU); unfold SEPTAB_A; lia | exact (shwL_now _ SHF) | apply (shwG_now _ FMT_RESP_A 16 SHWFMT MU); lia
    | apply (shz_sub _ (sh lo) (sh q) (sh lo) (sh q') (shzS_now _ MU)); [lia| apply sh_mono; lia]
    | apply (shr_sub _ _ (sh q + 8) _ (sh q' + 8) (shrS_now _ MU)); [lia| pose proof (sh_mono q' q ltac:(lia)); lia]
    | exact ST | exact MI | exact AE | exact RF | exact (fs_call_ok_push FI st stc tp 2%nat _ FCO LIVE1) | exact FE
    | reflexivity | reflexivity | reflexivity ]. }

  intros ms' PO. unfold match_resp_postA in PO.
  destruct PO as (r & cur' & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & st' & -> & MUc & WMc & MI' & FKc & LIVEc & RF' & ST' & AE' & SC' & RR & CR & ROK & RNOK & XR).
  clear SC LINE ST AE MI RF.

  fk_move FH FKc WMc.
  fk_move FT FKc WMc.
  fk_move SHF FKc WMc.
  fk_move FLG FKc WMc.
  fk_move MBC FKc WMc.
  fk_move RSC FKc WMc. fk_move SMC FKc WMc. fk_move VERC FKc WMc. fk_move CTLC FKc WMc.

  pose proof ABAND as ABu. unfold ABANDd in ABu.
  transport_after_call asegs m1 m' MUc WMc. clear MUc WMc ABu.
  replace (ret_pc (Z_to_bv 64 556108)) with (Z_to_bv 64 556108) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

  lazymatch goal with FKc : fkeep FI [_; _] stc m1 ?mm |- _ =>
    assert (FK' : fkeep FI WP st m0 mm);
    [ eapply (fkeep_trans FI WP st m0 m1 mm FK); eapply (fkeep_weaken_fk WP _ st stc m1 m0 mm FKc RF0 LSUB);
      apply Forall_cons; [left; cbn [inside fst snd]; clear; lia|];
      apply Forall_cons; [apply (new_frame_fk FI st 0 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl WP (F + 32) 16); cbn [FB_of SB_of]; left; clear; lia|];
      apply Forall_nil
    | clear FK FKc; rename FK' into FK ] end.
  rewrite LIVE1 in LIVEc.
  clear LVF LVS LVL PLB1 LSUB.
  destruct XR as (pa & pb & LINE & XR).
  step. step. if_cases K1; zify_cond K1.

  -
    apply (KEXIT r cur' m' (wz ty) (wz (A + cur1)) (wz tlz) pa pb); [lia| lia| mv_tacP| pv_tacP].
  -
    assert (X4 : r = 4) by (clear - K1 RR; rewrite ?unsigned_lit in K1 by lia; lia). subst r.
    destruct (XR eq_refl) as (o & l & -> & -> & XO1 & XO2 & XO3 & XO4 & XB).
    apply (KOK cur' o l m' (wz ty) (wz (A + cur1)) (wz tlz)); [lia| lia| lia| lia| exact XB| mv_tacP| pv_tacP].
Qed.

Notation zb := (Z_to_bv 8 0).
Notation set_byte := P0.H_presp_B.set_byte.
Definition pinvW (m : mem) (cur k sc maj min : Z) : Prop :=
  rw_cells asegs m (P + 480) [C8 (wz (P + 400)); C8 (wz cur); C4 (wz 0)]
  /\ rw_cells asegs m (P + 400) [C8 (wz A); C8 (wz len); C8 (wz cap); C8 (wz 5)]
  /\ rw_cells asegs m A [CB (Z.to_nat bn) (set_byte bs (Z.to_nat k) zb)]
  /\ bytes_at asegs m (A + bn) sl
  /\ rinvP m sc maj min.
Ltac pw_tacP := unfold pinvW; split; [eassumption|]; split; [eassumption|]; split; [assumption|]; split; [assumption| rv_tacP].

#[using="HC FI A lo bn bs sl st pad F FL SF AFS"] Lemma cb_split1 : forall m X (n : nat) (xs : list byte) (k : nat) (b : byte),
  rw_cells asegs m X [CB n xs] -> nth_error xs k = Some b -> 0 <= X ->
  rw_cells asegs m X [CB k (firstn k xs)] /\ rw_cells asegs m (X + Z.of_nat k) [CB 1 [b]; CB (n - k - 1) (skipn (k + 1) xs)].
Proof.
  intros m X n xs k b BLK Hb X0.
  assert (LXS : length xs = n) by (destruct BLK as [[W _] _]; cbn in W; LiaTuning.ctauto).
  pose proof (nth_error_Some_lt _ _ _ Hb) as LT.
  apply (rw_cells_split_CB asegs m X [] n xs [] [k; 1%nat; (n - k - 1)%nat]) in BLK; [| cbn; lia].
  cbn [app mk_CB_cells] in BLK.
  lazymatch type of BLK with rw_cells _ _ _ [?c1; ?c2; ?c3] =>
    destruct (proj1 (rw_cells_app asegs m X [c1] [c2; c3]) BLK) as [BLK1 BLK23] end.
  cbn [cells_size csize] in BLK23. rewrite Nat.add_0_r in BLK23.
  assert (E1 : firstn 1 (skipn k xs) = [b]).
  { destruct (nth_error_split _ _ _ Hb) as (pre & post & E & Hlen). rewrite E at 1. rewrite skipn_app, skipn_all2, Hlen, Nat.sub_diag by lia. reflexivity. }
  rewrite E1 in BLK23.
  replace (firstn (n - k - 1) (skipn 1 (skipn k xs))) with (skipn (k + 1) xs) in BLK23.
  2:{ rewrite skipn_skipn. replace (1 + k)%nat with (k + 1)%nat by lia. symmetry. apply firstn_all2. rewrite length_skipn. lia. }
  split; [exact BLK1| exact BLK23].
Qed.
#[using="HC FI lo bs sl st F FL SF"] Lemma cb_join1 : forall m X (n : nat) (xs : list byte) (k : nat) (b : byte),
  rw_cells asegs m X [CB k (firstn k xs)] -> rw_cells asegs m (X + Z.of_nat k) [CB 1 [b]; CB (n - k - 1) (skipn (k + 1) xs)] ->
  (k < n)%nat -> length xs = n ->
  rw_cells asegs m X [CB n (set_byte xs k b)].
Proof.
  intros m X n xs k b BLK1 BLK23 LT LXS.
  pose proof (proj2 (rw_cells_app asegs m X [CB k (firstn k xs)] [CB 1 [b]; CB (n - k - 1) (skipn (k + 1) xs)])) as J.
  cbn [cells_size csize Nat.add] in J. rewrite Nat.add_0_r in J. specialize (J (conj BLK1 BLK23)). cbn [app] in J.
  pose proof (rw_cells_merge asegs m X [] [CB k (firstn k xs); CB 1 [b]; CB (n - k - 1) (skipn (k + 1) xs)] []) as M.
  rewrite !app_nil_r in M. cbn [app cells_size csize cells_bytes cbytes Nat.add] in M.
  replace (k + Datatypes.S (n - k - 1 + 0))%nat with n in M by lia.
  pose proof (M J) as MJ. rewrite app_nil_r in MJ. exact MJ.
Qed.

#[using="CLO LO RF0 BN LBS SHWPo PHI PLB SHWA ALO AIMG ABHI AFS ABAND SLHI"] Lemma nulP : forall (o l cur' sc maj min : Z) (bcr : byte) q' m tyw tw1 tw2 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 (Q : machine_state -> Prop),
  0 <= o -> 0 <= l -> o + l < cur' -> cur' <= len -> nth_error bs (Z.to_nat (o + l)) = Some bcr ->
  minvP q' m tyw tw1 tw2 (wz (A + o)) (wz l) -> pinvP m cur' sc maj min ->
  (forall m' y11 y12 y13, minvP q' m' tyw tw1 tw2 (wz (A + o)) (wz l) -> pinvW m' cur' (o + l) sc maj min ->
     evt asegs Q (LSTP 0x87c90 q' x1 x5 x6 x7 (Z_to_bv 64 (A + (o + l))) y11 y12 y13 x14 x15 x16 x17 (Z_to_bv 64 (P + 480)) (Z_to_bv 64 4) (Z_to_bv 64 2) (Z_to_bv 64 (bv_unsigned bcr)) x28 x29 x30 x31 m')) ->
  evt asegs Q (LSTP 0x87c54 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (P + 480)) (Z_to_bv 64 4) (Z_to_bv 64 2) x27 x28 x29 x30 x31 m).
Proof.
  intros until Q; intros O0 L0 OL CL Hbcr INV PINV K.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j24 & j4 & QC) & TYC & TC & GAP & FRhi & FH & LINE & (j8 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (SC & MBC & TXC & SLK & (RSC & SMC & VERC & CTLC & (ev & ERRC))).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomP as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  assert (SHWT : shw m A len) by (apply (shw_frame_fs FI W0 m0 m A len (SHWA ltac:(lia)) MU W0_fsw); clear - AFS LBS; lia).
  assert (LBSn : length bs = Z.to_nat bn) by (clear - BN; lia).
  pose proof ABAND as ABu. unfold ABANDd in ABu. pose proof (AIMG ltac:(lia)) as AIMGu.
  pose proof (munch_refl [(A + (o + l), A + (o + l) + 1)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  hideW0 MU WM.
  destruct (cb_split1 m A (Z.to_nat bn) bs (Z.to_nat (o + l)) bcr TXC Hbcr ALO) as [TX1 TX23]. clear TXC.
  rewrite Z2Nat.id in TX23 by lia.
  remember (Z.to_nat bn - Z.to_nat (o + l) - 1)%nat as nr eqn:Enr.
  step. step. zstep.
  replace (Z_to_bv 64 (A + o + l)) with (Z_to_bv 64 (A + (o + l))) by (f_equal; lia).
  walk_ub_to 0x87c80.
  gen2 CONT 0x87c88 11%nat 12%nat.
  { intros yi yj.
    remember (A + (o + l)) as V eqn:EV.
    zstep.
    step; fix_lit_store.
    subst V.

    apply (rw_cells_reshape asegs _ _ _ [CB 1 [zb]; CB nr (skipn (Z.to_nat (o + l) + 1) bs)]) in TX23;
      [| destruct TX23 as [[W23 _] _]; cbn in W23 |- *; LiaTuning.ctauto | reflexivity | reflexivity].
    subst nr.
    pose proof (cb_join1 _ A (Z.to_nat bn) bs (Z.to_nat (o + l)) zb TX1 ltac:(rewrite Z2Nat.id by lia; exact TX23) ltac:(lia) LBSn) as TXC.
    clear TX1 TX23.
    destruct (liveP stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
    absorbW0 MU WM MU0 WM0 (sub_fp_text (A + (o + l)) (A + (o + l) + 1) ltac:(clear - O0 L0; lia) ltac:(clear - OL CL LBS; lia)).
    env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
    clear ABu AIMGu.
    apply K; [mv_tacP| pw_tacP]. }
  chkbN 11 (A + (o + l)) SHWT kk SHRk Hk.
  destruct Hk as [-> | [G1 G2]].
  - step. step. lit_branch. apply CONT.
  - step. rewrite (sxb_small kk) by lia.
    step. if_cases G3; zify_cond G3; [| exfalso; lia].
    zstep.
    step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
    apply CONT.
Qed.

Notation rtext := P0.F_shgetc_B.rtext.
Notation zbytes := P0.F_shgetc_A.zbytes.
Hypothesis SHWFMT2 : shw m0 FMT_SSCANF_A 11.
Hypothesis TPV : tp = Z_to_bv 64 6190512.
Variable canary : word.
Hypothesis SSPG : rw_cells asegs m0 got_sspA [C8 (wz ssp_guardA)].
Hypothesis SSPC : rw_cells asegs m0 ssp_guardA [C8 canary].

#[using="bs sl st CLO RF0 F FL SF PLB AIMG SSPG SSPC"] Lemma ssp_now : forall m, munch W0 m0 m -> wmono asegs m0 m -> (0 < len) ->
  rw_cells asegs m got_sspA [C8 (wz ssp_guardA)] /\ rw_cells asegs m ssp_guardA [C8 canary].
Proof.
  intros m MU WM HL. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomP as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  pose proof (AIMG HL) as AIMGu.
  split; [apply (rw_cells_transport asegs W0 m0 m _ _ SSPG MU WM)| apply (rw_cells_transport asegs W0 m0 m _ _ SSPC MU WM)];
    cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
    (repeat (split; [clear - CLO ACR FSB1 FSB2 ESHB EKB PFS1 AIMGu; lia|])); exact I.
Qed.

Notation s32v := P0.H_presp_B.s32v.
#[using="Type"] Lemma rw_cells_C4_s32vA : forall m X v, rw_cells asegs m X [C4 v] -> rw_cells asegs m X [C4 (Z_to_bv 64 (s32v v))].
Proof.
  intros m X v [[W B] R]. split; [split; [exact W|]| exact R]. cbn [cells_bytes cbytes] in *. rewrite <- P0.H_presp_B.le4_s32v. exact B.
Qed.

#[using="HC FI lo kE st F FL SF BN BNMAX SL7 SLAL"] Lemma line_rtext : forall (o l : Z), 0 <= o -> 0 <= l -> o + l < bn ->
  exists s rr, skipn (Z.to_nat o) (set_byte bs (Z.to_nat (o + l)) zb) = s ++ zb :: rr /\ ~ In zb s
    /\ rtext (A + o) (map bv_unsigned (skipn (Z.to_nat o) (set_byte bs (Z.to_nat (o + l)) zb) ++ sl)) (map bv_unsigned s) (map bv_unsigned (rr ++ sl))
    /\ Z.of_nat (length s) <= l.
Proof.
  intros o l O0 L0 KN. set (k := Z.to_nat (o + l)). set (bs1 := set_byte bs k zb).
  assert (LBSn : length bs = Z.to_nat bn) by (clear - BN; lia).
  assert (LB1 : length bs1 = length bs) by (subst bs1; apply P0.H_presp_B.set_byte_length; lia).
  assert (INZ : In zb (skipn (Z.to_nat o) bs1)).
  { apply (nth_error_In _ (Z.to_nat l)). rewrite P0.H_presp_B.nth_error_skipnZ. replace (Z.to_nat o + Z.to_nat l)%nat with k by lia.
    subst bs1. apply P0.H_presp_B.set_byte_same. lia. }
  destruct (P0.H_presp_B.first_nulB _ _ INZ) as (s & rr & SPLIT & NIN).
  exists s, rr. split; [exact SPLIT|]. split; [exact NIN|].
  assert (LS : (length s <= Z.to_nat l)%nat).
  { destruct (Nat.le_gt_cases (length s) (Z.to_nat l)) as [LE|GT]; [exact LE| exfalso]. apply NIN.
    apply (nth_error_In _ (Z.to_nat l)). rewrite <- (nth_error_app1 s (zb :: rr)) by lia. rewrite <- SPLIT, P0.H_presp_B.nth_error_skipnZ.
    replace (Z.to_nat o + Z.to_nat l)%nat with k by lia. subst bs1. apply P0.H_presp_B.set_byte_same. lia. }
  assert (LSK : length (skipn (Z.to_nat o) bs1) = (length s + 1 + length rr)%nat) by (rewrite SPLIT, length_app; cbn; lia).
  rewrite length_skipn in LSK.
  split; [| lia].
  unfold rtext. split.
  { rewrite SPLIT, <- app_assoc. cbn [app]. rewrite map_app. cbn [map]. replace (bv_unsigned zb) with 0%Z by (vm_compute; reflexivity). reflexivity. }
  split.
  { apply Forall_map. apply Forall_forall. intros bb Hbb. cbv beta. pose proof (P0.H_presp_A.byte_range bb) as R.
    assert (bb <> zb) by (intros ->; exact (NIN Hbb)). enough (bv_unsigned bb <> 0)%Z by lia.
    intros E. apply H. apply bv_eq. rewrite E. vm_compute. reflexivity. }
  split.
  { apply Forall_map. apply Forall_forall. intros bb _. cbv beta. pose proof (P0.H_presp_A.byte_range bb). lia. }
  split.
  { unfold Prelim.zlength. rewrite ?length_map, ?length_app, ?length_map.
    enough (HH : ((- (A + o + Z.of_nat (length s) + 1)) mod 8 <= A + bn + Z.of_nat (length sl) - (A + o + Z.of_nat (length s) + 1))%Z) by lia.
    set (N := (A + o + Z.of_nat (length s) + 1)%Z). set (E8 := (A + bn + Z.of_nat (length sl))%Z) in *.
    assert (HN : (N <= E8)%Z) by (subst N E8; lia).
    assert (AL8 : E8 mod 8 = 0) by (subst E8; rewrite SLAL; clear; Z.div_mod_to_equations; lia).
    rewrite <- (Z.mod_add (- N) (E8 / 8) 8) by lia.
    replace (- N + E8 / 8 * 8)%Z with (E8 - N)%Z by (clear - AL8; Z.div_mod_to_equations; lia).
    apply Z.mod_le; lia. }
  unfold Prelim.zlength. rewrite ?length_map, ?length_app, ?length_skipn.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR. lia.
Qed.

#[using="Type"] Lemma zbytes_bytesA : forall l : list byte, zbytes (map bv_unsigned l) = l.
Proof.
  intros l. unfold P0.F_shgetc_A.zbytes. rewrite map_map. rewrite <- (map_id l) at 2. apply map_ext. intros b.
  apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

#[using="IC kq kP kE CLO LO AL16 RF0 BN LBS BNMAX SHWPo PLO PHI PAL PLB SHWA ALO AIMG ABHI AFS ABAND SL7 SLHI SLAL SHZ SHR Q47 SHWFMT2 TPV canary SSPG SSPC"] Lemma scanfP : forall (o l cur' sc maj min : Z) q' m tyw tw1 tw2 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 (Q : machine_state -> Prop),
  0 <= o -> 0 <= l -> o + l < cur' -> cur' <= len ->
  minvP q' m tyw tw1 tw2 (wz (A + o)) (wz l) -> pinvW m cur' (o + l) sc maj min ->
  (forall (r : Z) (v1 v2 v3 : word) (s rr : list byte) m' y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
     skipn (Z.to_nat o) (set_byte bs (Z.to_nat (o + l)) zb) = s ++ zb :: rr -> ~ In zb s ->
     sscanf_model ScanInt.FMT_STATUSLINE (map bv_unsigned (skipn (Z.to_nat o) (set_byte bs (Z.to_nat (o + l)) zb) ++ sl)) (Prelim.zlength (map bv_unsigned s)) = Some r ->
     (r = -1 \/ 0 <= r <= 3) ->
     minvP q' m' tyw tw1 tw2 (wz (A + o)) (wz l) -> pinvW m' cur' (o + l) (s32v v3) (s32v v1) (s32v v2) ->
     evt asegs Q (LSTP 0x87cb8 q' y1 y5 y6 y7 (Z_to_bv 64 r) y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (P + 228)) (Z_to_bv 64 (P + 280)) (Z_to_bv 64 (P + 276)) x27 y28 y29 y30 y31 m')) ->
  evt asegs Q (LSTP 0x87c90 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 m).
Proof.
  intros until Q; intros O0 L0 OL CL INV PINV K.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j24 & j4 & QC) & TYC & TC & GAP & FRhi & FH & LINE & (j8 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (SC & MBC & TXC & SLK & (RSC & SMC & VERC & CTLC & (ev & ERRC))).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomP as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  pose proof (AIMG ltac:(lia)) as AIMGu.
  destruct (line_rtext o l O0 L0 ltac:(lia)) as (s & rr & SPLIT & NIN & TXT & LS).
  assert (LBSn : length bs = Z.to_nat bn) by (clear - BN; lia).
  assert (LB1 : length (set_byte bs (Z.to_nat (o + l)) zb) = Z.to_nat bn) by (rewrite P0.H_presp_B.set_byte_length; lia).
  remember (set_byte bs (Z.to_nat (o + l)) zb) as bs1 eqn:Ebs1.
  assert (BYT : bytes_at asegs m (A + o) (zbytes (map bv_unsigned (skipn (Z.to_nat o) bs1 ++ sl)))).
  { rewrite zbytes_bytesA. apply bytes_at_app. split.
    - pose proof (proj2 (proj1 TXC)) as BB1. cbn [cells_bytes cbytes] in BB1. rewrite app_nil_r in BB1.
      rewrite <- (firstn_skipn (Z.to_nat o) bs1) in BB1. apply bytes_at_app in BB1. destruct BB1 as [_ BB1].
      rewrite firstn_length_le in BB1 by lia. replace (A + Z.of_nat (Z.to_nat o))%Z with (A + o)%Z in BB1 by lia. exact BB1.
    - rewrite length_skipn. replace (A + o + Z.of_nat (length bs1 - Z.to_nat o))%Z with (A + bn)%Z by lia. exact SLK. }
  assert (LTXT : Prelim.zlength (map bv_unsigned (skipn (Z.to_nat o) bs1 ++ sl)) = bn - o + Z.of_nat (length sl)).
  { unfold Prelim.zlength. rewrite ?length_map, ?length_app, ?length_skipn. lia. }
  assert (LPRE : Prelim.zlength (map bv_unsigned s) = Z.of_nat (length s)) by (unfold Prelim.zlength; rewrite length_map; reflexivity).
  assert (SHWT : shw m A len) by (apply (shw_frame_fs FI W0 m0 m A len (SHWA ltac:(lia)) MU W0_fsw); clear - AFS LBS; lia).

  split_chunk VERC 2%nat VER0 VR1. split_chunk VR1 1%nat PMJ VR2. split_chunk VR2 1%nat PMN PPD.
  split_chunk RSC 1%nat RS0 PSC.
  do 10 step.
  destruct (liveP stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  pose proof (ssp_now m MU WM ltac:(lia)) as SSPN.
  assert (SHT1 : shw m (A + o) (Prelim.zlength (map bv_unsigned s) + 1)) by (rewrite LPRE; eapply shw_sub; [exact SHWT| lia| lia| lia]).
  assert (SHF1 : shw m FMT_SSCANF_A 11) by (apply (shwG_now _ FMT_SSCANF_A 11 SHWFMT2 MU); lia).
  assert (SHP1 : shw m (P + 276) 4) by (apply (shwP_now m (P + 276) 4 MU FK); lia).
  assert (SHP2 : shw m (P + 280) 4) by (apply (shwP_now m (P + 280) 4 MU FK); lia).
  assert (SHP3 : shw m (P + 228) 4) by (apply (shwP_now m (P + 228) 4 MU FK); lia).
  pose proof (shwStk_now m q' MU Hq) as SHWS.
  eapply evt_cut.
  { eapply (ic_sscanf_status IC) with (T := A + o) (txt := map bv_unsigned (skipn (Z.to_nat o) bs1 ++ sl)) (pre := map bv_unsigned s) (post := map bv_unsigned (rr ++ sl))
      (P1 := P + 276) (P2 := P + 280) (P3 := P + 228) (lox := lo) (qx := q');
    [ exact TXT | exact BYT
    | exact (proj1 SHT1) | exact (proj1 (proj2 SHT1)) | exact (proj2 (proj2 SHT1))
    | first [ lia | (unfold Prelim.zlength; rewrite ?length_map; lia) ]
    | exact (proj1 SHF1) | exact (proj1 (proj2 SHF1))
    | exact (proj1 SHP1) | exact (proj1 (proj2 SHP1)) | exact (proj2 (proj2 SHP1))
    | exact (proj1 SHP2) | exact (proj1 (proj2 SHP2)) | exact (proj2 (proj2 SHP2))
    | exact (proj1 SHP3) | exact (proj1 (proj2 SHP3)) | exact (proj2 (proj2 SHP3))
    | exact ST | exact MI | exact AE
    | exact CLO | unfold A0_SSCANF_DEPTH; lia | (clear - Hq32; Z.div_mod_to_equations; lia) | lia
    | clear - Hq Q47; lia | exact (proj1 SHWS) | exact (proj1 (proj2 SHWS))
    | exact TPV
    | (pose proof (AIMG ltac:(lia)) as AIMGx; lia) | rewrite LTXT; lia
    | lia | lia | lia
    | rewrite LTXT; clear - AFS PFS1 PFS2 SLAL SL7 EKB O0; lia | rewrite LTXT; clear - AFS PFS1 PFS2 SLAL SL7 EKB O0; lia | rewrite LTXT; clear - AFS PFS1 PFS2 SLAL SL7 EKB O0; lia
    | lia | lia | lia
    | exact (proj1 SSPN) | exact (proj2 SSPN) | exact ERRC
    | exact PMJ | exact PMN | exact PSC
    | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity ]. }
  intros ms' PO. unfold sscanf3_post_A, A0_ERRNO, A0_got_ssp, A0_ssp_guard in PO.
  destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & ev' & v1 & v2 & v3 & r & -> & MUc & WMc & MI' & ST' & AE' & _ & _ & SM & RR & _ & _ & ERRC' & PC1 & PC2 & PC3).
  pose proof MUc as MUt. pose proof WMc as WMt.
  fs_sync FI RF MUc WMc FK LSUB.
  clear PMJ PMN PSC ST AE MI BYT SHWT SSPN ERRC SHT1 SHF1 SHP1 SHP2 SHP3 SHWS.
  transport_after_call asegs m m' MUt WMt. clear MUt WMt.
  replace (ret_pc (Z_to_bv 64 556216)) with (Z_to_bv 64 556216) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  apply rw_cells_C4_s32vA in PC1. apply rw_cells_C4_s32vA in PC2. apply rw_cells_C4_s32vA in PC3.
  assert (VERC : rw_cells asegs m' (P + 264) [C8 (wz 0); C4 (wz isreq); C4 (wz (s32v v1)); C4 (wz (s32v v2)); C4 pad]).
  { apply (proj2 (rw_cells_app asegs m' (P + 264) [C8 (wz 0); C4 (wz isreq)] [C4 (wz (s32v v1)); C4 (wz (s32v v2)); C4 pad])). split; [exact VER0|].
    cbn [cells_size csize Nat.add]. replace (P + 264 + Z.of_nat 12)%Z with (P + 276)%Z by lia.
    apply (proj2 (rw_cells_app asegs m' (P + 276) [C4 (wz (s32v v1))] [C4 (wz (s32v v2)); C4 pad])). split; [exact PC1|].
    cbn [cells_size csize Nat.add]. replace (P + 276 + Z.of_nat 4)%Z with (P + 280)%Z by lia.
    apply (proj2 (rw_cells_app asegs m' (P + 280) [C4 (wz (s32v v2))] [C4 pad])). split; [exact PC2|].
    cbn [cells_size csize Nat.add]. replace (P + 280 + Z.of_nat 4)%Z with (P + 284)%Z by lia. exact PPD. }
  assert (RSC : rw_cells asegs m' (P + 224) [C4 (wz rm); C4 (wz (s32v v3))]).
  { apply (proj2 (rw_cells_app asegs m' (P + 224) [C4 (wz rm)] [C4 (wz (s32v v3))])). split; [exact RS0|].
    cbn [cells_size csize Nat.add]. replace (P + 224 + Z.of_nat 4)%Z with (P + 228)%Z by lia. exact PC3. }
  clear VER0 PC1 PC2 PPD RS0 PC3.
  subst bs1.
  apply (K r v1 v2 v3 s rr m'); [exact SPLIT| exact NIN| rewrite LPRE in SM |- *; exact SM| exact RR| mv_tacP| pw_tacP].
Qed.

#[using="CLO LO RF0 BN LBS SHWPo PHI PLB SHWA ALO AIMG ABHI AFS ABAND SLHI"] Lemma restoreP : forall (o l cur' sc maj min r : Z) (bcr : byte) q' m tyw tw1 tw2 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (Q : machine_state -> Prop),
  0 <= o -> 0 <= l -> o + l < cur' -> cur' <= len -> nth_error bs (Z.to_nat (o + l)) = Some bcr -> (r = -1 \/ 0 <= r <= 3) ->
  minvP q' m tyw tw1 tw2 (wz (A + o)) (wz l) -> pinvW m cur' (o + l) sc maj min ->
  (forall m' y11 y12 y13 y14, r <> 3 -> minvP q' m' tyw tw1 tw2 (wz (A + o)) (wz l) -> pinvP m' cur' sc maj min ->
     evt asegs Q (LSTP 0x88094 q' x1 x5 x6 x7 (Z_to_bv 64 3) y11 y12 y13 y14 x15 x16 x17 (Z_to_bv 64 (P + 228)) (Z_to_bv 64 (P + 280)) (Z_to_bv 64 (P + 276)) (Z_to_bv 64 (bv_unsigned bcr)) x28 x29 x30 x31 m')) ->
  (forall m' y11 y12 y13 y14, r = 3 -> minvP q' m' tyw tw1 tw2 (wz (A + o)) (wz l) -> pinvP m' cur' sc maj min ->
     evt asegs Q (LSTP 0x87cfc q' x1 x5 x6 x7 (Z_to_bv 64 3) y11 y12 y13 y14 x15 x16 x17 (Z_to_bv 64 (P + 228)) (Z_to_bv 64 (P + 280)) (Z_to_bv 64 (P + 276)) (Z_to_bv 64 (bv_unsigned bcr)) x28 x29 x30 x31 m')) ->
  evt asegs Q (LSTP 0x87cb8 q' x1 x5 x6 x7 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (P + 228)) (Z_to_bv 64 (P + 280)) (Z_to_bv 64 (P + 276)) (Z_to_bv 64 (bv_unsigned bcr)) x28 x29 x30 x31 m).
Proof.
  intros until Q; intros O0 L0 OL CL Hbcr RR INV PINV KEXIT KOK.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j24 & j4 & QC) & TYC & TC & GAP & FRhi & FH & LINE & (j8 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (SC & MBC & TXC & SLK & (RSC & SMC & VERC & CTLC & (ev & ERRC))).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomP as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  pose proof ABAND as ABu. unfold ABANDd in ABu. pose proof (AIMG ltac:(lia)) as AIMGu.
  pose proof (munch_refl [(A + (o + l), A + (o + l) + 1)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  hideW0 MU WM.
  assert (SHWT : shw m A len) by (apply (shw_frame_fs FI W0 m0 m A len (SHWA ltac:(lia)) MU W0_fsw); clear - AFS LBS; lia).
  assert (LBSn : length bs = Z.to_nat bn) by (clear - BN; lia).
  pose proof (bv_unsigned_in_range 8 bcr) as BR. unfold bv_modulus in BR. cbn in BR.
  remember (set_byte bs (Z.to_nat (o + l)) zb) as bs1 eqn:Ebs1.
  assert (LB1 : length bs1 = Z.to_nat bn) by (subst bs1; rewrite P0.H_presp_B.set_byte_length; lia).
  assert (Hz : nth_error bs1 (Z.to_nat (o + l)) = Some zb) by (subst bs1; apply P0.H_presp_B.set_byte_same; lia).
  destruct (cb_split1 m A (Z.to_nat bn) bs1 (Z.to_nat (o + l)) zb TXC Hz ALO) as [TX1 TX23]. clear TXC.
  rewrite Z2Nat.id in TX23 by lia.
  remember (Z.to_nat bn - Z.to_nat (o + l) - 1)%nat as nr eqn:Enr.
  step. step. zstep.
  replace (Z_to_bv 64 (A + o + l)) with (Z_to_bv 64 (A + (o + l))) by (f_equal; lia).
  walk_ub_to 0x87ce8.
  gen2 CONT 0x87cf0 10%nat 13%nat.
  { intros yi yj.
    step.
    remember (A + (o + l)) as V eqn:EV.
    step. rewrite le1_zxb. mem_after_store. subst V.
    apply (rw_cells_reshape asegs _ _ _ [CB 1 [bcr]; CB nr (skipn (Z.to_nat (o + l) + 1) bs1)]) in TX23; [| destruct TX23 as [[W23 _] _]; cbn in W23 |- *; LiaTuning.ctauto | reflexivity | reflexivity].
    subst nr.
    pose proof (cb_join1 _ A (Z.to_nat bn) bs1 (Z.to_nat (o + l)) bcr TX1 ltac:(rewrite Z2Nat.id by lia; exact TX23) ltac:(lia) LB1) as TXC.
    clear TX1 TX23.
    assert (RESTORE : set_byte bs1 (Z.to_nat (o + l)) bcr = bs) by (subst bs1; apply P0.H_presp_B.set_byte_restore; exact Hbcr).
    rewrite RESTORE in TXC. clear RESTORE.
    destruct (liveP stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
    absorbW0 MU WM MU0 WM0 (sub_fp_text (A + (o + l)) (A + (o + l) + 1) ltac:(clear - O0 L0; lia) ltac:(clear - OL CL LBS; lia)).
    env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
    clear ABu AIMGu.
    step. if_cases K3; zify_cond K3.
    - assert (R3 : r <> 3) by (clear - K3; intros ->; evalK K3; lia).
      apply (KEXIT m1); [exact R3| mv_tacP| pv_tacP].
    - assert (R3 : r = 3) by (clear - K3 RR; assert (C : r = -1 \/ r = 0 \/ r = 1 \/ r = 2 \/ r = 3) by lia; destruct C as [->|[->|[->|[->| ->]]]]; evalK K3; lia).
      apply (KOK m1); [exact R3| mv_tacP| pv_tacP]. }
  chkbN 10 (A + (o + l)) SHWT kk SHRk Hk.
  destruct Hk as [-> | [G1 G2]].
  - step. step. lit_branch. apply CONT.
  - step. rewrite (sxb_small kk) by lia.
    step. if_cases G3; zify_cond G3; [| exfalso; lia].
    zstep.
    step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
    apply CONT.
Qed.

#[using="kP RF0 SHWPo PLO PHI PAL PLB ALO ABAND"] Lemma signsP : forall (cur' sc maj min : Z) q' m tyw tw1 tw2 lb ll x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 (Q : machine_state -> Prop),
  - 2^31 <= sc < 2^31 -> - 2^31 <= maj < 2^31 -> - 2^31 <= min < 2^31 ->
  minvP q' m tyw tw1 tw2 lb ll -> pinvP m cur' sc maj min ->
  (forall y11, (maj < 0 \/ min < 0 \/ sc < 0) ->
     evt asegs Q (LSTP 0x88094 q' x1 x5 x6 x7 (Z_to_bv 64 3) y11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (P + 228)) (Z_to_bv 64 (P + 280)) (Z_to_bv 64 (P + 276)) x27 x28 x29 x30 x31 m)) ->
  (forall y11, 0 <= maj -> 0 <= min -> 0 <= sc ->
     evt asegs Q (LSTP 0x87d44 q' x1 x5 x6 x7 (Z_to_bv 64 3) y11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (P + 228)) (Z_to_bv 64 (P + 280)) (Z_to_bv 64 (P + 276)) x27 x28 x29 x30 x31 m)) ->
  evt asegs Q (LSTP 0x87cfc q' x1 x5 x6 x7 (Z_to_bv 64 3) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (P + 228)) (Z_to_bv 64 (P + 280)) (Z_to_bv 64 (P + 276)) x27 x28 x29 x30 x31 m).
Proof.
  intros until Q; intros SR MR NR INV PINV KEXIT KOK.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j24 & j4 & QC) & TYC & TC & GAP & FRhi & FH & LINE & (j8 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (SC & MBC & TXC & SLK & (RSC & SMC & VERC & CTLC & (ev & ERRC))).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (SHWP : shw m P 504) by (apply (shwP_now m P 504 MU FK); lia).
  step. step. chk8N 11 (P + 276) SHWP. step. lit_branch.
  step. rewrite (sx32_lit maj) by lia.
  step. if_cases K1; zify_cond K1.
  { assert (N1 : maj < 0) by (destruct (Z_lt_le_dec maj 0) as [X|X]; [exact X| rewrite P0.H_presp_A.land64_nonneg in K1 by lia; lia]).
    apply KEXIT. lia. }
  assert (P1 : 0 <= maj) by (destruct (Z_lt_le_dec maj 0) as [X|X]; [rewrite P0.H_presp_A.land64_neg in K1 by lia; lia| exact X]). clear K1.
  step. step. chk8N 11 (P + 280) SHWP. step. lit_branch.
  step. rewrite (sx32_lit min) by lia.
  step. if_cases K2; zify_cond K2.
  { assert (N2 : min < 0) by (destruct (Z_lt_le_dec min 0) as [X|X]; [exact X| rewrite P0.H_presp_A.land64_nonneg in K2 by lia; lia]).
    apply KEXIT. lia. }
  assert (P2 : 0 <= min) by (destruct (Z_lt_le_dec min 0) as [X|X]; [rewrite P0.H_presp_A.land64_neg in K2 by lia; lia| exact X]). clear K2.
  step. step. chk8N 11 (P + 228) SHWP. step. lit_branch.
  step. rewrite (sx32_lit sc) by lia.
  step. if_cases K3; zify_cond K3.
  { assert (N3 : sc < 0) by (destruct (Z_lt_le_dec sc 0) as [X|X]; [exact X| rewrite P0.H_presp_A.land64_nonneg in K3 by lia; lia]).
    apply KEXIT. lia. }
  assert (P3 : 0 <= sc) by (destruct (Z_lt_le_dec sc 0) as [X|X]; [rewrite P0.H_presp_A.land64_neg in K3 by lia; lia| exact X]). clear K3.
  apply KOK; assumption.
Qed.

Notation bdig := P0.H_presp_A.bdig.
Notation bndig := P0.H_presp_A.bndig.

#[using="HC FI lo bs sl st F FL SF"] Lemma ndig_test : forall b : Z, 0 <= b < 256 ->
  (Z.land (b + -58) 18446744073709551615 < 18446744073709551606 <-> (b < 48 \/ 57 < b)).
Proof.
  intros b Hb. destruct (Z_lt_le_dec (b + -58) 0) as [N|N].
  - rewrite P0.H_presp_A.land64_neg by lia. lia.
  - rewrite P0.H_presp_A.land64_nonneg by lia. lia.
Qed.
#[using="HC FI lo bs sl st F FL SF"] Lemma dig_test : forall b : Z, 0 <= b < 256 ->
  (Z.land (b + -48) 18446744073709551615 < 10 <-> (48 <= b <= 57)).
Proof.
  intros b Hb. destruct (Z_lt_le_dec (b + -48) 0) as [N|N].
  - rewrite P0.H_presp_A.land64_neg by lia. lia.
  - rewrite P0.H_presp_A.land64_nonneg by lia. lia.
Qed.

#[using="HC FI lo bs sl st F FL SF"] Lemma dig_test2 : forall b : Z, 0 <= b < 256 ->
  (18446744073709551605 < Z.land (b + -58) 18446744073709551615 <-> (48 <= b <= 57)).
Proof.
  intros b Hb. destruct (Z_lt_le_dec (b + -58) 0) as [N|N].
  - rewrite P0.H_presp_A.land64_neg by lia. lia.
  - rewrite P0.H_presp_A.land64_nonneg by lia. lia.
Qed.
#[using="HC FI lo bs sl st F FL SF"] Lemma ndig_test2 : forall b : Z, 0 <= b < 256 ->
  (9 < Z.land (b + -48) 18446744073709551615 <-> (b < 48 \/ 57 < b)).
Proof.
  intros b Hb. destruct (Z_lt_le_dec (b + -48) 0) as [N|N].
  - rewrite P0.H_presp_A.land64_neg by lia. lia.
  - rewrite P0.H_presp_A.land64_nonneg by lia. lia.
Qed.

#[using="lo bn sl FL LBS AIMG ABHI SLHI"] Lemma walkL1 : forall (k : nat) (t o j : Z) q' m x1 x5 x6 x7 x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 (Q : machine_state -> Prop),
  j - t < Z.of_nat k -> 0 <= t -> t < j -> j < len ->
  mem_inv asegs m -> bytes_at asegs m A bs -> shw m A len ->
  (forall u, t < u < j -> bndig bs u) -> bdig bs j ->
  (forall y16 y17,
     evt asegs Q (LSTP 0x87dbc q' x1 x5 x6 x7 (Z_to_bv 64 3) (Z_to_bv 64 (A + j)) (Z_to_bv 64 (A + o)) (Z_to_bv 64 (A + j + 1)) (Z_to_bv 64 (-1)) (Z_to_bv 64 (-10)) y16 y17 x21 x22 x23 x27 x28 x29 x30 x31 m)) ->
  evt asegs Q (LSTP 0x87d80 q' x1 x5 x6 x7 (Z_to_bv 64 3) (Z_to_bv 64 (A + t)) (Z_to_bv 64 (A + o)) (Z_to_bv 64 (A + t + 1)) (Z_to_bv 64 (-1)) (Z_to_bv 64 (-10)) x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 m).
Proof.
  induction k as [|k IH]; intros until Q; intros HK HT0 HT HJ MI BUF SHWT INS OUT K; [lia|].
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (bytes_at_bound _ _ _ _ BUF) as BB. pose proof (AIMG ltac:(lia)) as AIMGu.
  assert (HB : exists b, nth_error bs (Z.to_nat (t + 1)) = Some b /\ ((t + 1 < j /\ (bv_unsigned b < 48 \/ 57 < bv_unsigned b)) \/ (t + 1 = j /\ 48 <= bv_unsigned b <= 57))).
  { destruct (Z.eq_dec (t + 1) j) as [E|NE].
    - destruct OUT as (b & Hb & R). exists b. rewrite E. split; [exact Hb| right; split; [reflexivity| exact R]].
    - destruct (INS (t + 1) ltac:(lia)) as (b & Hb & R). exists b. split; [exact Hb| left; split; [lia| exact R]]. }
  destruct HB as (b & Hb & HBR). pose proof (P0.H_presp_A.byte_range b) as BR.
  pose proof (u8ro_read asegs m A bs (t + 1) b (Z_to_bv 64 (A + t + 1)) BUF Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  step. ubr.
  step. step.
  gen2 CONT 0x87d94 16%nat 17%nat.
  { intros y16 y17.
    zstep. step. zstep. zstep.
    step. if_cases K1; zify_cond K1.
    - apply (ndig_test (bv_unsigned b) BR) in K1.
      destruct HBR as [[TL _]|[E X]]; [| exfalso; lia].
      replace (Z_to_bv 64 (A + t + 2)) with (Z_to_bv 64 (A + (t + 1) + 1)) by (f_equal; lia).
      replace (Z_to_bv 64 (A + t + 1)) with (Z_to_bv 64 (A + (t + 1))) by (f_equal; lia).
      apply (IH (t + 1) o j); try assumption; [lia| lia| intros u Hu; apply INS; lia].
    - assert (DGT : 48 <= bv_unsigned b <= 57) by (pose proof (ndig_test (bv_unsigned b) BR) as X; lia).
      destruct HBR as [[_ X]|[E _]]; [exfalso; lia|].
      step.
      replace (Z_to_bv 64 (A + t + 2)) with (Z_to_bv 64 (A + j + 1)) by (f_equal; lia).
      replace (Z_to_bv 64 (A + t + 1)) with (Z_to_bv 64 (A + j)) by (f_equal; lia).
      apply K. }
  chkbN 16 (A + t + 1) SHWT kk SHRk Hk.
  destruct Hk as [-> | [G1 G2]].
  - step. step. lit_branch. apply CONT.
  - step. rewrite (sxb_small kk) by lia.
    step. if_cases G3; zify_cond G3; [| exfalso; lia].
    zstep.
    step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
    apply CONT.
Qed.

#[using="lo bn sl FL LBS AIMG ABHI SLHI"] Lemma walkL2 : forall (k : nat) (t o j : Z) q' m x1 x5 x6 x7 x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 (Q : machine_state -> Prop),
  j - t < Z.of_nat k -> 0 <= t -> t < j -> j < len ->
  mem_inv asegs m -> bytes_at asegs m A bs -> shw m A len ->
  (forall u, t < u < j -> bdig bs u) -> bndig bs j ->
  (forall y16 y17,
     evt asegs Q (LSTP 0x87e24 q' x1 x5 x6 x7 (Z_to_bv 64 3) (Z_to_bv 64 (A + j)) (Z_to_bv 64 (A + o)) (Z_to_bv 64 (A + j + 1)) (Z_to_bv 64 (-1)) (Z_to_bv 64 (10)) y16 y17 x21 x22 x23 x27 x28 x29 x30 x31 m)) ->
  evt asegs Q (LSTP 0x87de8 q' x1 x5 x6 x7 (Z_to_bv 64 3) (Z_to_bv 64 (A + t)) (Z_to_bv 64 (A + o)) (Z_to_bv 64 (A + t + 1)) (Z_to_bv 64 (-1)) (Z_to_bv 64 (10)) x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 m).
Proof.
  induction k as [|k IH]; intros until Q; intros HK HT0 HT HJ MI BUF SHWT INS OUT K; [lia|].
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (bytes_at_bound _ _ _ _ BUF) as BB. pose proof (AIMG ltac:(lia)) as AIMGu.
  assert (HB : exists b, nth_error bs (Z.to_nat (t + 1)) = Some b /\ ((t + 1 < j /\ 48 <= bv_unsigned b <= 57) \/ (t + 1 = j /\ (bv_unsigned b < 48 \/ 57 < bv_unsigned b)))).
  { destruct (Z.eq_dec (t + 1) j) as [E|NE].
    - destruct OUT as (b & Hb & R). exists b. rewrite E. split; [exact Hb| right; split; [reflexivity| exact R]].
    - destruct (INS (t + 1) ltac:(lia)) as (b & Hb & R). exists b. split; [exact Hb| left; split; [lia| exact R]]. }
  destruct HB as (b & Hb & HBR). pose proof (P0.H_presp_A.byte_range b) as BR.
  pose proof (u8ro_read asegs m A bs (t + 1) b (Z_to_bv 64 (A + t + 1)) BUF Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  step. ubr.
  step. step.
  gen2 CONT 0x87dfc 16%nat 17%nat.
  { intros y16 y17.
    zstep. step. zstep. zstep.
    step. if_cases K1; zify_cond K1.
    - apply (dig_test (bv_unsigned b) BR) in K1.
      destruct HBR as [[TL _]|[E X]]; [| exfalso; lia].
      replace (Z_to_bv 64 (A + t + 2)) with (Z_to_bv 64 (A + (t + 1) + 1)) by (f_equal; lia).
      replace (Z_to_bv 64 (A + t + 1)) with (Z_to_bv 64 (A + (t + 1))) by (f_equal; lia).
      apply (IH (t + 1) o j); try assumption; [lia| lia| intros u Hu; apply INS; lia].
    - assert (DGT : (bv_unsigned b < 48 \/ 57 < bv_unsigned b)) by (pose proof (dig_test (bv_unsigned b) BR) as X; lia).
      destruct HBR as [[_ X]|[E _]]; [exfalso; lia|].
      step.
      replace (Z_to_bv 64 (A + t + 2)) with (Z_to_bv 64 (A + j + 1)) by (f_equal; lia).
      replace (Z_to_bv 64 (A + t + 1)) with (Z_to_bv 64 (A + j)) by (f_equal; lia).
      apply K. }
  chkbN 16 (A + t + 1) SHWT kk SHRk Hk.
  destruct Hk as [-> | [G1 G2]].
  - step. step. lit_branch. apply CONT.
  - step. rewrite (sxb_small kk) by lia.
    step. if_cases G3; zify_cond G3; [| exfalso; lia].
    zstep.
    step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
    apply CONT.
Qed.

#[using="lo bn sl FL LBS AIMG ABHI SLHI"] Lemma walkH2 : forall (t o j : Z) q' m x1 x5 x6 x7 x13 x14 x15 x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 (Q : machine_state -> Prop),
  0 <= t -> t <= j -> j < len ->
  mem_inv asegs m -> bytes_at asegs m A bs -> shw m A len ->
  (forall u, t <= u < j -> bdig bs u) -> bndig bs j ->
  (forall y13 y14 y15 y16 y17,
     evt asegs Q (LSTP 0x87e24 q' x1 x5 x6 x7 (Z_to_bv 64 3) (Z_to_bv 64 (A + j)) (Z_to_bv 64 (A + o)) y13 y14 y15 y16 y17 x21 x22 x23 x27 x28 x29 x30 x31 m)) ->
  evt asegs Q (LSTP 0x87dbc q' x1 x5 x6 x7 (Z_to_bv 64 3) (Z_to_bv 64 (A + t)) (Z_to_bv 64 (A + o)) x13 x14 x15 x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 m).
Proof.
  intros until Q; intros HT0 HT HJ MI BUF SHWT INS OUT K.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (bytes_at_bound _ _ _ _ BUF) as BB. pose proof (AIMG ltac:(lia)) as AIMGu.
  assert (HB : exists b, nth_error bs (Z.to_nat t) = Some b /\ ((t < j /\ 48 <= bv_unsigned b <= 57) \/ (t = j /\ (bv_unsigned b < 48 \/ 57 < bv_unsigned b)))).
  { destruct (Z.eq_dec t j) as [E|NE].
    - destruct OUT as (b & Hb & R). exists b. rewrite E. split; [exact Hb| right; split; [reflexivity| exact R]].
    - destruct (INS t ltac:(lia)) as (b & Hb & R). exists b. split; [exact Hb| left; split; [lia| exact R]]. }
  destruct HB as (b & Hb & HBR). pose proof (P0.H_presp_A.byte_range b) as BR.
  pose proof (u8ro_read asegs m A bs t b (Z_to_bv 64 (A + t)) BUF Hb ltac:(lia) eq_refl) as RD.
  step. step.
  gen2 CONT 0x87dcc 13%nat 14%nat.
  { intros y13 y14.
    step. zstep. step.
    step. if_cases K1; zify_cond K1.
    - apply (ndig_test2 (bv_unsigned b) BR) in K1.
      destruct HBR as [[_ X]|[E _]]; [exfalso; lia|]. subst j.
      apply K.
    - assert (DGT : 48 <= bv_unsigned b <= 57) by (pose proof (ndig_test2 (bv_unsigned b) BR) as X; lia).
      destruct HBR as [[TL _]|[_ X]]; [| exfalso; lia].
      step. step. step.
      apply (walkL2 (Datatypes.S (Z.to_nat (j - t))) t o j); try assumption; [lia| intros u Hu; apply INS; lia|].
      intros z16 z17. apply K. }
  chkbN 13 (A + t) SHWT kk SHRk Hk.
  destruct Hk as [-> | [G1 G2]].
  - step. step. lit_branch. apply CONT.
  - step. rewrite (sxb_small kk) by lia.
    step. if_cases G3; zify_cond G3; [| exfalso; lia].
    zstep.
    step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
    apply CONT.
Qed.

#[using="lo bn sl FL LBS AIMG ABHI SLHI"] Lemma walkL3 : forall (k : nat) (t o j : Z) q' m x1 x5 x6 x7 x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 (Q : machine_state -> Prop),
  j - t < Z.of_nat k -> 0 <= t -> t < j -> j < len ->
  mem_inv asegs m -> bytes_at asegs m A bs -> shw m A len ->
  (forall u, t < u < j -> bndig bs u) -> bdig bs j ->
  (forall y16 y17,
     evt asegs Q (LSTP 0x87e8c q' x1 x5 x6 x7 (Z_to_bv 64 3) (Z_to_bv 64 (A + j)) (Z_to_bv 64 (A + o)) (Z_to_bv 64 (A + j + 1)) (Z_to_bv 64 (-1)) (Z_to_bv 64 (-10)) y16 y17 x21 x22 x23 x27 x28 x29 x30 x31 m)) ->
  evt asegs Q (LSTP 0x87e50 q' x1 x5 x6 x7 (Z_to_bv 64 3) (Z_to_bv 64 (A + t)) (Z_to_bv 64 (A + o)) (Z_to_bv 64 (A + t + 1)) (Z_to_bv 64 (-1)) (Z_to_bv 64 (-10)) x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 m).
Proof.
  induction k as [|k IH]; intros until Q; intros HK HT0 HT HJ MI BUF SHWT INS OUT K; [lia|].
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (bytes_at_bound _ _ _ _ BUF) as BB. pose proof (AIMG ltac:(lia)) as AIMGu.
  assert (HB : exists b, nth_error bs (Z.to_nat (t + 1)) = Some b /\ ((t + 1 < j /\ (bv_unsigned b < 48 \/ 57 < bv_unsigned b)) \/ (t + 1 = j /\ 48 <= bv_unsigned b <= 57))).
  { destruct (Z.eq_dec (t + 1) j) as [E|NE].
    - destruct OUT as (b & Hb & R). exists b. rewrite E. split; [exact Hb| right; split; [reflexivity| exact R]].
    - destruct (INS (t + 1) ltac:(lia)) as (b & Hb & R). exists b. split; [exact Hb| left; split; [lia| exact R]]. }
  destruct HB as (b & Hb & HBR). pose proof (P0.H_presp_A.byte_range b) as BR.
  pose proof (u8ro_read asegs m A bs (t + 1) b (Z_to_bv 64 (A + t + 1)) BUF Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  step. ubr.
  step. step.
  gen2 CONT 0x87e64 16%nat 17%nat.
  { intros y16 y17.
    zstep. step. zstep. zstep.
    step. if_cases K1; zify_cond K1.
    - apply (ndig_test (bv_unsigned b) BR) in K1.
      destruct HBR as [[TL _]|[E X]]; [| exfalso; lia].
      replace (Z_to_bv 64 (A + t + 2)) with (Z_to_bv 64 (A + (t + 1) + 1)) by (f_equal; lia).
      replace (Z_to_bv 64 (A + t + 1)) with (Z_to_bv 64 (A + (t + 1))) by (f_equal; lia).
      apply (IH (t + 1) o j); try assumption; [lia| lia| intros u Hu; apply INS; lia].
    - assert (DGT : 48 <= bv_unsigned b <= 57) by (pose proof (ndig_test (bv_unsigned b) BR) as X; lia).
      destruct HBR as [[_ X]|[E _]]; [exfalso; lia|].
      step.
      replace (Z_to_bv 64 (A + t + 2)) with (Z_to_bv 64 (A + j + 1)) by (f_equal; lia).
      replace (Z_to_bv 64 (A + t + 1)) with (Z_to_bv 64 (A + j)) by (f_equal; lia).
      apply K. }
  chkbN 16 (A + t + 1) SHWT kk SHRk Hk.
  destruct Hk as [-> | [G1 G2]].
  - step. step. lit_branch. apply CONT.
  - step. rewrite (sxb_small kk) by lia.
    step. if_cases G3; zify_cond G3; [| exfalso; lia].
    zstep.
    step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
    apply CONT.
Qed.

#[using="lo bn sl FL LBS AIMG ABHI SLHI"] Lemma walkH3 : forall (t o j : Z) q' m x1 x5 x6 x7 x13 x14 x15 x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 (Q : machine_state -> Prop),
  0 <= t -> t <= j -> j < len ->
  mem_inv asegs m -> bytes_at asegs m A bs -> shw m A len ->
  (forall u, t <= u < j -> bndig bs u) -> bdig bs j ->
  (forall y13 y14 y15 y16 y17,
     evt asegs Q (LSTP 0x87e8c q' x1 x5 x6 x7 (Z_to_bv 64 3) (Z_to_bv 64 (A + j)) (Z_to_bv 64 (A + o)) y13 y14 y15 y16 y17 x21 x22 x23 x27 x28 x29 x30 x31 m)) ->
  evt asegs Q (LSTP 0x87e24 q' x1 x5 x6 x7 (Z_to_bv 64 3) (Z_to_bv 64 (A + t)) (Z_to_bv 64 (A + o)) x13 x14 x15 x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 m).
Proof.
  intros until Q; intros HT0 HT HJ MI BUF SHWT INS OUT K.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (bytes_at_bound _ _ _ _ BUF) as BB. pose proof (AIMG ltac:(lia)) as AIMGu.
  assert (HB : exists b, nth_error bs (Z.to_nat t) = Some b /\ ((t < j /\ (bv_unsigned b < 48 \/ 57 < bv_unsigned b)) \/ (t = j /\ 48 <= bv_unsigned b <= 57))).
  { destruct (Z.eq_dec t j) as [E|NE].
    - destruct OUT as (b & Hb & R). exists b. rewrite E. split; [exact Hb| right; split; [reflexivity| exact R]].
    - destruct (INS t ltac:(lia)) as (b & Hb & R). exists b. split; [exact Hb| left; split; [lia| exact R]]. }
  destruct HB as (b & Hb & HBR). pose proof (P0.H_presp_A.byte_range b) as BR.
  pose proof (u8ro_read asegs m A bs t b (Z_to_bv 64 (A + t)) BUF Hb ltac:(lia) eq_refl) as RD.
  step. step.
  gen2 CONT 0x87e34 13%nat 14%nat.
  { intros y13 y14.
    step. zstep. step.
    step. if_cases K1; zify_cond K1.
    - apply (dig_test2 (bv_unsigned b) BR) in K1.
      destruct HBR as [[_ X]|[E _]]; [exfalso; lia|]. subst j.
      apply K.
    - assert (DGT : (bv_unsigned b < 48 \/ 57 < bv_unsigned b)) by (pose proof (dig_test2 (bv_unsigned b) BR) as X; lia).
      destruct HBR as [[TL _]|[_ X]]; [| exfalso; lia].
      step. step. step.
      apply (walkL3 (Datatypes.S (Z.to_nat (j - t))) t o j); try assumption; [lia| intros u Hu; apply INS; lia|].
      intros z16 z17. apply K. }
  chkbN 13 (A + t) SHWT kk SHRk Hk.
  destruct Hk as [-> | [G1 G2]].
  - step. step. lit_branch. apply CONT.
  - step. rewrite (sxb_small kk) by lia.
    step. if_cases G3; zify_cond G3; [| exfalso; lia].
    zstep.
    step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
    apply CONT.
Qed.

#[using="lo bn sl FL LBS AIMG ABHI SLHI"] Lemma walkL4 : forall (k : nat) (t o j : Z) q' m x1 x5 x6 x7 x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 (Q : machine_state -> Prop),
  j - t < Z.of_nat k -> 0 <= t -> t < j -> j < len ->
  mem_inv asegs m -> bytes_at asegs m A bs -> shw m A len ->
  (forall u, t < u < j -> bdig bs u) -> bndig bs j ->
  (forall y16 y17,
     evt asegs Q (LSTP 0x87ef4 q' x1 x5 x6 x7 (Z_to_bv 64 3) (Z_to_bv 64 (A + j)) (Z_to_bv 64 (A + o)) (Z_to_bv 64 (A + j + 1)) (Z_to_bv 64 (-1)) (Z_to_bv 64 (10)) y16 y17 x21 x22 x23 x27 x28 x29 x30 x31 m)) ->
  evt asegs Q (LSTP 0x87eb8 q' x1 x5 x6 x7 (Z_to_bv 64 3) (Z_to_bv 64 (A + t)) (Z_to_bv 64 (A + o)) (Z_to_bv 64 (A + t + 1)) (Z_to_bv 64 (-1)) (Z_to_bv 64 (10)) x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 m).
Proof.
  induction k as [|k IH]; intros until Q; intros HK HT0 HT HJ MI BUF SHWT INS OUT K; [lia|].
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (bytes_at_bound _ _ _ _ BUF) as BB. pose proof (AIMG ltac:(lia)) as AIMGu.
  assert (HB : exists b, nth_error bs (Z.to_nat (t + 1)) = Some b /\ ((t + 1 < j /\ 48 <= bv_unsigned b <= 57) \/ (t + 1 = j /\ (bv_unsigned b < 48 \/ 57 < bv_unsigned b)))).
  { destruct (Z.eq_dec (t + 1) j) as [E|NE].
    - destruct OUT as (b & Hb & R). exists b. rewrite E. split; [exact Hb| right; split; [reflexivity| exact R]].
    - destruct (INS (t + 1) ltac:(lia)) as (b & Hb & R). exists b. split; [exact Hb| left; split; [lia| exact R]]. }
  destruct HB as (b & Hb & HBR). pose proof (P0.H_presp_A.byte_range b) as BR.
  pose proof (u8ro_read asegs m A bs (t + 1) b (Z_to_bv 64 (A + t + 1)) BUF Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  step. ubr.
  step. step.
  gen2 CONT 0x87ecc 16%nat 17%nat.
  { intros y16 y17.
    zstep. step. zstep. zstep.
    step. if_cases K1; zify_cond K1.
    - apply (dig_test (bv_unsigned b) BR) in K1.
      destruct HBR as [[TL _]|[E X]]; [| exfalso; lia].
      replace (Z_to_bv 64 (A + t + 2)) with (Z_to_bv 64 (A + (t + 1) + 1)) by (f_equal; lia).
      replace (Z_to_bv 64 (A + t + 1)) with (Z_to_bv 64 (A + (t + 1))) by (f_equal; lia).
      apply (IH (t + 1) o j); try assumption; [lia| lia| intros u Hu; apply INS; lia].
    - assert (DGT : (bv_unsigned b < 48 \/ 57 < bv_unsigned b)) by (pose proof (dig_test (bv_unsigned b) BR) as X; lia).
      destruct HBR as [[_ X]|[E _]]; [exfalso; lia|].
      step.
      replace (Z_to_bv 64 (A + t + 2)) with (Z_to_bv 64 (A + j + 1)) by (f_equal; lia).
      replace (Z_to_bv 64 (A + t + 1)) with (Z_to_bv 64 (A + j)) by (f_equal; lia).
      apply K. }
  chkbN 16 (A + t + 1) SHWT kk SHRk Hk.
  destruct Hk as [-> | [G1 G2]].
  - step. step. lit_branch. apply CONT.
  - step. rewrite (sxb_small kk) by lia.
    step. if_cases G3; zify_cond G3; [| exfalso; lia].
    zstep.
    step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
    apply CONT.
Qed.

#[using="lo bn sl FL LBS AIMG ABHI SLHI"] Lemma walkH4 : forall (t o j : Z) q' m x1 x5 x6 x7 x13 x14 x15 x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 (Q : machine_state -> Prop),
  0 <= t -> t <= j -> j < len ->
  mem_inv asegs m -> bytes_at asegs m A bs -> shw m A len ->
  (forall u, t <= u < j -> bdig bs u) -> bndig bs j ->
  (forall y13 y14 y15 y16 y17,
     evt asegs Q (LSTP 0x87ef4 q' x1 x5 x6 x7 (Z_to_bv 64 3) (Z_to_bv 64 (A + j)) (Z_to_bv 64 (A + o)) y13 y14 y15 y16 y17 x21 x22 x23 x27 x28 x29 x30 x31 m)) ->
  evt asegs Q (LSTP 0x87e8c q' x1 x5 x6 x7 (Z_to_bv 64 3) (Z_to_bv 64 (A + t)) (Z_to_bv 64 (A + o)) x13 x14 x15 x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 m).
Proof.
  intros until Q; intros HT0 HT HJ MI BUF SHWT INS OUT K.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (bytes_at_bound _ _ _ _ BUF) as BB. pose proof (AIMG ltac:(lia)) as AIMGu.
  assert (HB : exists b, nth_error bs (Z.to_nat t) = Some b /\ ((t < j /\ 48 <= bv_unsigned b <= 57) \/ (t = j /\ (bv_unsigned b < 48 \/ 57 < bv_unsigned b)))).
  { destruct (Z.eq_dec t j) as [E|NE].
    - destruct OUT as (b & Hb & R). exists b. rewrite E. split; [exact Hb| right; split; [reflexivity| exact R]].
    - destruct (INS t ltac:(lia)) as (b & Hb & R). exists b. split; [exact Hb| left; split; [lia| exact R]]. }
  destruct HB as (b & Hb & HBR). pose proof (P0.H_presp_A.byte_range b) as BR.
  pose proof (u8ro_read asegs m A bs t b (Z_to_bv 64 (A + t)) BUF Hb ltac:(lia) eq_refl) as RD.
  step. step.
  gen2 CONT 0x87e9c 13%nat 14%nat.
  { intros y13 y14.
    step. zstep. step.
    step. if_cases K1; zify_cond K1.
    - apply (ndig_test2 (bv_unsigned b) BR) in K1.
      destruct HBR as [[_ X]|[E _]]; [exfalso; lia|]. subst j.
      apply K.
    - assert (DGT : 48 <= bv_unsigned b <= 57) by (pose proof (ndig_test2 (bv_unsigned b) BR) as X; lia).
      destruct HBR as [[TL _]|[_ X]]; [| exfalso; lia].
      step. step. step.
      apply (walkL4 (Datatypes.S (Z.to_nat (j - t))) t o j); try assumption; [lia| intros u Hu; apply INS; lia|].
      intros z16 z17. apply K. }
  chkbN 13 (A + t) SHWT kk SHRk Hk.
  destruct Hk as [-> | [G1 G2]].
  - step. step. lit_branch. apply CONT.
  - step. rewrite (sxb_small kk) by lia.
    step. if_cases G3; zify_cond G3; [| exfalso; lia].
    zstep.
    step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
    apply CONT.
Qed.

#[using="lo bn sl FL LBS AIMG ABHI SLHI"] Lemma walkL5 : forall (k : nat) (t o j : Z) q' m x1 x5 x6 x7 x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 (Q : machine_state -> Prop),
  j - t < Z.of_nat k -> 0 <= t -> t < j -> j < len ->
  mem_inv asegs m -> bytes_at asegs m A bs -> shw m A len ->
  (forall u, t < u < j -> bndig bs u) -> bdig bs j ->
  (forall y16 y17,
     evt asegs Q (LSTP 0x87f5c q' x1 x5 x6 x7 (Z_to_bv 64 3) (Z_to_bv 64 (A + j)) (Z_to_bv 64 (A + o)) (Z_to_bv 64 (A + j + 1)) (Z_to_bv 64 (-1)) (Z_to_bv 64 (-10)) y16 y17 x21 x22 x23 x27 x28 x29 x30 x31 m)) ->
  evt asegs Q (LSTP 0x87f20 q' x1 x5 x6 x7 (Z_to_bv 64 3) (Z_to_bv 64 (A + t)) (Z_to_bv 64 (A + o)) (Z_to_bv 64 (A + t + 1)) (Z_to_bv 64 (-1)) (Z_to_bv 64 (-10)) x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 m).
Proof.
  induction k as [|k IH]; intros until Q; intros HK HT0 HT HJ MI BUF SHWT INS OUT K; [lia|].
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (bytes_at_bound _ _ _ _ BUF) as BB. pose proof (AIMG ltac:(lia)) as AIMGu.
  assert (HB : exists b, nth_error bs (Z.to_nat (t + 1)) = Some b /\ ((t + 1 < j /\ (bv_unsigned b < 48 \/ 57 < bv_unsigned b)) \/ (t + 1 = j /\ 48 <= bv_unsigned b <= 57))).
  { destruct (Z.eq_dec (t + 1) j) as [E|NE].
    - destruct OUT as (b & Hb & R). exists b. rewrite E. split; [exact Hb| right; split; [reflexivity| exact R]].
    - destruct (INS (t + 1) ltac:(lia)) as (b & Hb & R). exists b. split; [exact Hb| left; split; [lia| exact R]]. }
  destruct HB as (b & Hb & HBR). pose proof (P0.H_presp_A.byte_range b) as BR.
  pose proof (u8ro_read asegs m A bs (t + 1) b (Z_to_bv 64 (A + t + 1)) BUF Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  step. ubr.
  step. step.
  gen2 CONT 0x87f34 16%nat 17%nat.
  { intros y16 y17.
    zstep. step. zstep. zstep.
    step. if_cases K1; zify_cond K1.
    - apply (ndig_test (bv_unsigned b) BR) in K1.
      destruct HBR as [[TL _]|[E X]]; [| exfalso; lia].
      replace (Z_to_bv 64 (A + t + 2)) with (Z_to_bv 64 (A + (t + 1) + 1)) by (f_equal; lia).
      replace (Z_to_bv 64 (A + t + 1)) with (Z_to_bv 64 (A + (t + 1))) by (f_equal; lia).
      apply (IH (t + 1) o j); try assumption; [lia| lia| intros u Hu; apply INS; lia].
    - assert (DGT : 48 <= bv_unsigned b <= 57) by (pose proof (ndig_test (bv_unsigned b) BR) as X; lia).
      destruct HBR as [[_ X]|[E _]]; [exfalso; lia|].
      step.
      replace (Z_to_bv 64 (A + t + 2)) with (Z_to_bv 64 (A + j + 1)) by (f_equal; lia).
      replace (Z_to_bv 64 (A + t + 1)) with (Z_to_bv 64 (A + j)) by (f_equal; lia).
      apply K. }
  chkbN 16 (A + t + 1) SHWT kk SHRk Hk.
  destruct Hk as [-> | [G1 G2]].
  - step. step. lit_branch. apply CONT.
  - step. rewrite (sxb_small kk) by lia.
    step. if_cases G3; zify_cond G3; [| exfalso; lia].
    zstep.
    step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
    apply CONT.
Qed.

#[using="lo bn sl FL LBS AIMG ABHI SLHI"] Lemma walkH5 : forall (t o j : Z) q' m x1 x5 x6 x7 x13 x14 x15 x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 (Q : machine_state -> Prop),
  0 <= t -> t <= j -> j < len ->
  mem_inv asegs m -> bytes_at asegs m A bs -> shw m A len ->
  (forall u, t <= u < j -> bndig bs u) -> bdig bs j ->
  (forall y13 y14 y15 y16 y17,
     evt asegs Q (LSTP 0x87f5c q' x1 x5 x6 x7 (Z_to_bv 64 3) (Z_to_bv 64 (A + j)) (Z_to_bv 64 (A + o)) y13 y14 y15 y16 y17 x21 x22 x23 x27 x28 x29 x30 x31 m)) ->
  evt asegs Q (LSTP 0x87ef4 q' x1 x5 x6 x7 (Z_to_bv 64 3) (Z_to_bv 64 (A + t)) (Z_to_bv 64 (A + o)) x13 x14 x15 x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 m).
Proof.
  intros until Q; intros HT0 HT HJ MI BUF SHWT INS OUT K.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (bytes_at_bound _ _ _ _ BUF) as BB. pose proof (AIMG ltac:(lia)) as AIMGu.
  assert (HB : exists b, nth_error bs (Z.to_nat t) = Some b /\ ((t < j /\ (bv_unsigned b < 48 \/ 57 < bv_unsigned b)) \/ (t = j /\ 48 <= bv_unsigned b <= 57))).
  { destruct (Z.eq_dec t j) as [E|NE].
    - destruct OUT as (b & Hb & R). exists b. rewrite E. split; [exact Hb| right; split; [reflexivity| exact R]].
    - destruct (INS t ltac:(lia)) as (b & Hb & R). exists b. split; [exact Hb| left; split; [lia| exact R]]. }
  destruct HB as (b & Hb & HBR). pose proof (P0.H_presp_A.byte_range b) as BR.
  pose proof (u8ro_read asegs m A bs t b (Z_to_bv 64 (A + t)) BUF Hb ltac:(lia) eq_refl) as RD.
  step. step.
  gen2 CONT 0x87f04 13%nat 14%nat.
  { intros y13 y14.
    step. zstep. step.
    step. if_cases K1; zify_cond K1.
    - apply (dig_test2 (bv_unsigned b) BR) in K1.
      destruct HBR as [[_ X]|[E _]]; [exfalso; lia|]. subst j.
      apply K.
    - assert (DGT : (bv_unsigned b < 48 \/ 57 < bv_unsigned b)) by (pose proof (dig_test2 (bv_unsigned b) BR) as X; lia).
      destruct HBR as [[TL _]|[_ X]]; [| exfalso; lia].
      step. step. step.
      apply (walkL5 (Datatypes.S (Z.to_nat (j - t))) t o j); try assumption; [lia| intros u Hu; apply INS; lia|].
      intros z16 z17. apply K. }
  chkbN 13 (A + t) SHWT kk SHRk Hk.
  destruct Hk as [-> | [G1 G2]].
  - step. step. lit_branch. apply CONT.
  - step. rewrite (sxb_small kk) by lia.
    step. if_cases G3; zify_cond G3; [| exfalso; lia].
    zstep.
    step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
    apply CONT.
Qed.

#[using="lo bn sl FL LBS AIMG ABHI SLHI"] Lemma walkL6 : forall (k : nat) (t o j : Z) q' m x1 x5 x6 x7 x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 (Q : machine_state -> Prop),
  j - t < Z.of_nat k -> 0 <= t -> t < j -> j < len ->
  mem_inv asegs m -> bytes_at asegs m A bs -> shw m A len ->
  (forall u, t < u < j -> bdig bs u) -> bndig bs j ->
  (forall y16 y17,
     evt asegs Q (LSTP 0x87fc4 q' x1 x5 x6 x7 (Z_to_bv 64 3) (Z_to_bv 64 (A + j)) (Z_to_bv 64 (A + o)) (Z_to_bv 64 (A + j + 1)) (Z_to_bv 64 (-1)) (Z_to_bv 64 (10)) y16 y17 x21 x22 x23 x27 x28 x29 x30 x31 m)) ->
  evt asegs Q (LSTP 0x87f88 q' x1 x5 x6 x7 (Z_to_bv 64 3) (Z_to_bv 64 (A + t)) (Z_to_bv 64 (A + o)) (Z_to_bv 64 (A + t + 1)) (Z_to_bv 64 (-1)) (Z_to_bv 64 (10)) x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 m).
Proof.
  induction k as [|k IH]; intros until Q; intros HK HT0 HT HJ MI BUF SHWT INS OUT K; [lia|].
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (bytes_at_bound _ _ _ _ BUF) as BB. pose proof (AIMG ltac:(lia)) as AIMGu.
  assert (HB : exists b, nth_error bs (Z.to_nat (t + 1)) = Some b /\ ((t + 1 < j /\ 48 <= bv_unsigned b <= 57) \/ (t + 1 = j /\ (bv_unsigned b < 48 \/ 57 < bv_unsigned b)))).
  { destruct (Z.eq_dec (t + 1) j) as [E|NE].
    - destruct OUT as (b & Hb & R). exists b. rewrite E. split; [exact Hb| right; split; [reflexivity| exact R]].
    - destruct (INS (t + 1) ltac:(lia)) as (b & Hb & R). exists b. split; [exact Hb| left; split; [lia| exact R]]. }
  destruct HB as (b & Hb & HBR). pose proof (P0.H_presp_A.byte_range b) as BR.
  pose proof (u8ro_read asegs m A bs (t + 1) b (Z_to_bv 64 (A + t + 1)) BUF Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  step. ubr.
  step. step.
  gen2 CONT 0x87f9c 16%nat 17%nat.
  { intros y16 y17.
    zstep. step. zstep. zstep.
    step. if_cases K1; zify_cond K1.
    - apply (dig_test (bv_unsigned b) BR) in K1.
      destruct HBR as [[TL _]|[E X]]; [| exfalso; lia].
      replace (Z_to_bv 64 (A + t + 2)) with (Z_to_bv 64 (A + (t + 1) + 1)) by (f_equal; lia).
      replace (Z_to_bv 64 (A + t + 1)) with (Z_to_bv 64 (A + (t + 1))) by (f_equal; lia).
      apply (IH (t + 1) o j); try assumption; [lia| lia| intros u Hu; apply INS; lia].
    - assert (DGT : (bv_unsigned b < 48 \/ 57 < bv_unsigned b)) by (pose proof (dig_test (bv_unsigned b) BR) as X; lia).
      destruct HBR as [[_ X]|[E _]]; [exfalso; lia|].
      step.
      replace (Z_to_bv 64 (A + t + 2)) with (Z_to_bv 64 (A + j + 1)) by (f_equal; lia).
      replace (Z_to_bv 64 (A + t + 1)) with (Z_to_bv 64 (A + j)) by (f_equal; lia).
      apply K. }
  chkbN 16 (A + t + 1) SHWT kk SHRk Hk.
  destruct Hk as [-> | [G1 G2]].
  - step. step. lit_branch. apply CONT.
  - step. rewrite (sxb_small kk) by lia.
    step. if_cases G3; zify_cond G3; [| exfalso; lia].
    zstep.
    step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
    apply CONT.
Qed.

#[using="lo bn sl FL LBS AIMG ABHI SLHI"] Lemma walkH6 : forall (t o j : Z) q' m x1 x5 x6 x7 x13 x14 x15 x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 (Q : machine_state -> Prop),
  0 <= t -> t <= j -> j < len ->
  mem_inv asegs m -> bytes_at asegs m A bs -> shw m A len ->
  (forall u, t <= u < j -> bdig bs u) -> bndig bs j ->
  (forall y13 y14 y15 y16 y17,
     evt asegs Q (LSTP 0x87fc4 q' x1 x5 x6 x7 (Z_to_bv 64 3) (Z_to_bv 64 (A + j)) (Z_to_bv 64 (A + o)) y13 y14 y15 y16 y17 x21 x22 x23 x27 x28 x29 x30 x31 m)) ->
  evt asegs Q (LSTP 0x87f5c q' x1 x5 x6 x7 (Z_to_bv 64 3) (Z_to_bv 64 (A + t)) (Z_to_bv 64 (A + o)) x13 x14 x15 x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 m).
Proof.
  intros until Q; intros HT0 HT HJ MI BUF SHWT INS OUT K.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (bytes_at_bound _ _ _ _ BUF) as BB. pose proof (AIMG ltac:(lia)) as AIMGu.
  assert (HB : exists b, nth_error bs (Z.to_nat t) = Some b /\ ((t < j /\ 48 <= bv_unsigned b <= 57) \/ (t = j /\ (bv_unsigned b < 48 \/ 57 < bv_unsigned b)))).
  { destruct (Z.eq_dec t j) as [E|NE].
    - destruct OUT as (b & Hb & R). exists b. rewrite E. split; [exact Hb| right; split; [reflexivity| exact R]].
    - destruct (INS t ltac:(lia)) as (b & Hb & R). exists b. split; [exact Hb| left; split; [lia| exact R]]. }
  destruct HB as (b & Hb & HBR). pose proof (P0.H_presp_A.byte_range b) as BR.
  pose proof (u8ro_read asegs m A bs t b (Z_to_bv 64 (A + t)) BUF Hb ltac:(lia) eq_refl) as RD.
  step. step.
  gen2 CONT 0x87f6c 13%nat 14%nat.
  { intros y13 y14.
    step. zstep. step.
    step. if_cases K1; zify_cond K1.
    - apply (ndig_test2 (bv_unsigned b) BR) in K1.
      destruct HBR as [[_ X]|[E _]]; [exfalso; lia|]. subst j.
      apply K.
    - assert (DGT : 48 <= bv_unsigned b <= 57) by (pose proof (ndig_test2 (bv_unsigned b) BR) as X; lia).
      destruct HBR as [[TL _]|[_ X]]; [| exfalso; lia].
      step. step. step.
      apply (walkL6 (Datatypes.S (Z.to_nat (j - t))) t o j); try assumption; [lia| intros u Hu; apply INS; lia|].
      intros z16 z17. apply K. }
  chkbN 13 (A + t) SHWT kk SHRk Hk.
  destruct Hk as [-> | [G1 G2]].
  - step. step. lit_branch. apply CONT.
  - step. rewrite (sxb_small kk) by lia.
    step. if_cases G3; zify_cond G3; [| exfalso; lia].
    zstep.
    step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
    apply CONT.
Qed.

#[using="lo bn sl FL LBS AIMG ABHI SLHI"] Lemma walkH1 : forall (o l j : Z) q' m x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 (Q : machine_state -> Prop),
  0 <= o -> o <= j -> j < len ->
  mem_inv asegs m -> bytes_at asegs m A bs -> shw m A len ->
  rw_cells asegs m (F + 32) [C8 (wz (A + o)); C8 (wz l)] ->
  (forall u, o <= u < j -> bndig bs u) -> bdig bs j ->
  (forall y13 y14 y15 y16 y17,
     evt asegs Q (LSTP 0x87dbc q' x1 x5 x6 x7 (Z_to_bv 64 3) (Z_to_bv 64 (A + j)) (Z_to_bv 64 (A + o)) y13 y14 y15 y16 y17 x21 x22 x23 x27 x28 x29 x30 x31 m)) ->
  evt asegs Q (LSTP 0x87d44 q' x1 x5 x6 x7 (Z_to_bv 64 3) x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 m).
Proof.
  intros until Q; intros HT0 HT HJ MI BUF SHWT LINE INS OUT K.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (bytes_at_bound _ _ _ _ BUF) as BB. pose proof (AIMG ltac:(lia)) as AIMGu.
  assert (HB : exists b, nth_error bs (Z.to_nat o) = Some b /\ ((o < j /\ (bv_unsigned b < 48 \/ 57 < bv_unsigned b)) \/ (o = j /\ 48 <= bv_unsigned b <= 57))).
  { destruct (Z.eq_dec o j) as [E|NE].
    - destruct OUT as (b & Hb & R). exists b. rewrite E. split; [exact Hb| right; split; [reflexivity| exact R]].
    - destruct (INS o ltac:(lia)) as (b & Hb & R). exists b. split; [exact Hb| left; split; [lia| exact R]]. }
  destruct HB as (b & Hb & HBR). pose proof (P0.H_presp_A.byte_range b) as BR.
  pose proof (u8ro_read asegs m A bs o b (Z_to_bv 64 (A + o)) BUF Hb ltac:(lia) eq_refl) as RD.
  step.
  step. ubr.
  step. step.
  gen2 CONT 0x87d5c 11%nat 13%nat.
  { intros y11 y13.
    step. zstep. step. step.
    step. if_cases K1; zify_cond K1.
    - apply (dig_test2 (bv_unsigned b) BR) in K1.
      destruct HBR as [[_ X]|[E _]]; [exfalso; lia|]. subst j.
      apply K.
    - assert (DGT : (bv_unsigned b < 48 \/ 57 < bv_unsigned b)) by (pose proof (dig_test2 (bv_unsigned b) BR) as X; lia).
      destruct HBR as [[TL _]|[_ X]]; [| exfalso; lia].
      zstep. step. step. step.
      apply (walkL1 (Datatypes.S (Z.to_nat (j - o))) o o j); try assumption; [lia| intros u Hu; apply INS; lia|].
      intros z16 z17. apply K. }
  chkbN 11 (A + o) SHWT kk SHRk Hk.
  destruct Hk as [-> | [G1 G2]].
  - step. step. lit_branch. apply CONT.
  - step. rewrite (sxb_small kk) by lia.
    step. if_cases G3; zify_cond G3; [| exfalso; lia].
    zstep.
    step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
    apply CONT.
Qed.
Notation bblank := P0.H_presp_A.bblank.

#[using="lo bn sl FL BN LBS AIMG ABHI SLHI"] Lemma walkL7 : forall (k : nat) (u o e : Z) q' m x1 x5 x6 x7 x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 (Q : machine_state -> Prop),
  e - u < Z.of_nat k -> 0 <= u -> u <= e -> e < len ->
  mem_inv asegs m -> bytes_at asegs m A bs -> shw m A len ->
  (exists be, nth_error bs (Z.to_nat e) = Some be /\ ~ bblank be) ->
  (forall t' bt' y17, u <= t' <= e -> nth_error bs (Z.to_nat t') = Some bt' -> ~ bblank bt' ->
     evt asegs Q (LSTP 0x88038 q' x1 x5 x6 x7 (Z_to_bv 64 (A + t')) (Z_to_bv 64 (A + t')) (Z_to_bv 64 (A + o)) (Z_to_bv 64 32) (Z_to_bv 64 (-1)) (Z_to_bv 64 9)
                       (Z_to_bv 64 (bv_unsigned bt')) y17 x21 x22 x23 x27 x28 x29 x30 x31 m)) ->
  evt asegs Q (LSTP 0x88004 q' x1 x5 x6 x7 (Z_to_bv 64 (A + u)) (Z_to_bv 64 (A + u)) (Z_to_bv 64 (A + o)) (Z_to_bv 64 32) (Z_to_bv 64 (-1)) (Z_to_bv 64 9) x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 m).
Proof.
  induction k as [|k IH]; intros until Q; intros HK HU HT HJ MI BUF SHWT HE K; [lia|].
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (bytes_at_bound _ _ _ _ BUF) as BB. pose proof (AIMG ltac:(lia)) as AIMGu.
  assert (HB : exists b, nth_error bs (Z.to_nat u) = Some b).
  { destruct (nth_error bs (Z.to_nat u)) as [b|] eqn:E; [exists b; reflexivity| exfalso].
    apply nth_error_None in E. destruct HE as (be & Hbe & _). pose proof (nth_error_Some_lt _ _ _ Hbe). lia. }
  destruct HB as (b & Hb). pose proof (P0.H_presp_A.byte_range b) as BR.
  pose proof (u8ro_read asegs m A bs u b (Z_to_bv 64 (A + u)) BUF Hb ltac:(lia) eq_refl) as RD.
  assert (BD : bblank b \/ ~ bblank b) by (unfold P0.H_presp_A.bblank; lia).
  destruct BD as [BL|NBL].
  - assert (UE : u < e).
    { destruct (Z.eq_dec u e) as [->|NE]; [| lia]. exfalso. destruct HE as (be & Hbe & NB). rewrite Hb in Hbe. injection Hbe as <-. exact (NB BL). }
    gen2 CONT 0x88010 16%nat 17%nat.
    { intros y16 y17.
      step. ubr.
      zstep. zstep. step. step.
      replace (Z_to_bv 64 (A + u + 1)) with (Z_to_bv 64 (A + (u + 1))) by (f_equal; lia).
      chkbN 16 (A + (u + 1)) SHWT kk SHRk Hk.
      destruct Hk as [-> | [G1 G2]].
      + step. step. lit_branch.
        apply (IH (u + 1) o e); try assumption; [lia| lia| lia|].
        intros t' bt' z17 HT' HBT NBT. apply (K t' bt' z17); [lia| exact HBT| exact NBT].
      + step. rewrite (sxb_small kk) by lia.
        step. if_cases G3; zify_cond G3; [exfalso; lia|].
        zstep.
        step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
        apply (IH (u + 1) o e); try assumption; [lia| lia| lia|].
        intros t' bt' z17 HT' HBT NBT. apply (K t' bt' z17); [lia| exact HBT| exact NBT]. }
    step.
    step. if_cases K1; zify_cond K1; [apply CONT|].
    step. if_cases K2; zify_cond K2; [| apply CONT].
    exfalso. rewrite unsigned_lit in K1, K2 by lia. unfold P0.H_presp_A.bblank in BL. lia.
  - step.
    step. if_cases K1; zify_cond K1.
    { exfalso. rewrite unsigned_lit in K1 by lia. unfold P0.H_presp_A.bblank in NBL. lia. }
    step. if_cases K2; zify_cond K2.
    2:{ exfalso. rewrite unsigned_lit in K2 by lia. unfold P0.H_presp_A.bblank in NBL. lia. }
    apply (K u b x17); [lia| exact Hb| exact NBL].
Qed.

#[using="lo bn sl FL BN LBS AIMG ABHI SLHI"] Lemma walkB : forall (u o e : Z) q' m x1 x5 x6 x7 x14 x15 x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 (Q : machine_state -> Prop),
  0 <= u -> u <= e -> e < len ->
  mem_inv asegs m -> bytes_at asegs m A bs -> shw m A len ->
  (exists be, nth_error bs (Z.to_nat e) = Some be /\ ~ bblank be) ->
  (forall t' bt' y17, u <= t' <= e -> nth_error bs (Z.to_nat t') = Some bt' -> ~ bblank bt' ->
     evt asegs Q (LSTP 0x88038 q' x1 x5 x6 x7 (Z_to_bv 64 (A + t')) (Z_to_bv 64 (A + t')) (Z_to_bv 64 (A + o)) (Z_to_bv 64 32) (Z_to_bv 64 (-1)) (Z_to_bv 64 9)
                       (Z_to_bv 64 (bv_unsigned bt')) y17 x21 x22 x23 x27 x28 x29 x30 x31 m)) ->
  evt asegs Q (LSTP 0x87fe8 q' x1 x5 x6 x7 (Z_to_bv 64 3) (Z_to_bv 64 (A + u)) (Z_to_bv 64 (A + o)) (Z_to_bv 64 32) x14 x15 x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 m).
Proof.
  intros until Q; intros HU HT HJ MI BUF SHWT HE K.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (bytes_at_bound _ _ _ _ BUF) as BB. pose proof (AIMG ltac:(lia)) as AIMGu.
  step. step. step. step. step.
  gen2 CONT 0x88004 16%nat 17%nat.
  { intros y16 y17. apply (walkL7 (Datatypes.S (Z.to_nat (e - u))) u o e); try assumption. lia. }
  chkbN 16 (A + u) SHWT kk SHRk Hk.
  destruct Hk as [-> | [G1 G2]].
  - step. step. lit_branch. apply CONT.
  - step. rewrite (sxb_small kk) by lia.
    step. if_cases G3; zify_cond G3; [| exfalso; lia].
    zstep.
    step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
    apply CONT.
Qed.

#[using="lo bn sl FL BN LBS AIMG ABHI SLHI"] Lemma walkP : forall (o l j1 e1 j2 e2 j3 e3 : Z) (be : byte) q' m x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 (Q : machine_state -> Prop),
  P0.H_presp_A.runs3 bs o j1 e1 j2 e2 j3 e3 -> e3 <= o + l -> o + l < len ->
  nth_error bs (Z.to_nat (o + l)) = Some be -> ~ bblank be ->
  mem_inv asegs m -> bytes_at asegs m A bs -> shw m A len ->
  rw_cells asegs m (F + 32) [C8 (wz (A + o)); C8 (wz l)] ->
  (forall y5 y11 y12 y13 y14 y15 y16 y17,
     evt asegs Q (LSTP 0x88094 q' x1 y5 x6 x7 (Z_to_bv 64 3) y11 y12 y13 y14 y15 y16 y17 x21 x22 x23 x27 x28 x29 x30 x31 m)) ->
  (forall t' bt' y5 y17, e3 <= t' <= o + l -> nth_error bs (Z.to_nat t') = Some bt' -> ~ bblank bt' ->
     evt asegs Q (LSTP 0x88038 q' x1 y5 x6 x7 (Z_to_bv 64 (A + t')) (Z_to_bv 64 (A + t')) (Z_to_bv 64 (A + o)) (Z_to_bv 64 32) (Z_to_bv 64 (-1)) (Z_to_bv 64 9)
                       (Z_to_bv 64 (bv_unsigned bt')) y17 x21 x22 x23 x27 x28 x29 x30 x31 m)) ->
  evt asegs Q (LSTP 0x87d44 q' x1 x5 x6 x7 (Z_to_bv 64 3) x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 m).
Proof.
  intros until Q; intros RU E3 OL Hbe NBE MI BUF SHWT LINE KEXIT KOK.
  destruct RU as (ORD & N1 & D1 & R1 & X1 & N2 & D2 & R2 & X2 & N3 & D3 & R3 & X3).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (bytes_at_bound _ _ _ _ BUF) as BB. pose proof (AIMG ltac:(lia)) as AIMGu.
  apply (walkH1 o l j1); try assumption; [lia| lia| lia|].
  intros a13 a14 a15 a16 a17.
  apply (walkH2 j1 o e1); try assumption; [lia| lia| lia|].
  intros b13 b14 b15 b16 b17.
  apply (walkH3 e1 o j2); try assumption; [lia| lia| lia|].
  intros c13 c14 c15 c16 c17.
  apply (walkH4 j2 o e2); try assumption; [lia| lia| lia|].
  intros d13 d14 d15 d16 d17.
  apply (walkH5 e2 o j3); try assumption; [lia| lia| lia|].
  intros e13 e14 e15 e16 e17.
  apply (walkH6 j3 o e3); try assumption; [lia| lia| lia| |].
  { intros v Hv. destruct (Z.eq_dec v j3) as [->|NE]; [exact D3| apply R3; lia]. }
  intros f13 f14 f15 f16 f17.

  destruct X3 as (b3 & Hb3 & NDG3). pose proof (P0.H_presp_A.byte_range b3) as BR3.
  pose proof (u8ro_read asegs m A bs e3 b3 (Z_to_bv 64 (A + e3)) BUF Hb3 ltac:(lia) eq_refl) as RD3.
  step. step.
  gen2 CONT 0x87fd4 13%nat 14%nat.
  { intros w13 w14.
    step. step.
    step. if_cases K1; zify_cond K1.
    - apply (walkB e3 o (o + l)); try assumption; [lia| exists be; split; [exact Hbe| exact NBE]|].
      intros t' bt' g17 HT' HBT NBT. apply (KOK t' bt'); [lia| exact HBT| exact NBT].
    - step. step. if_cases K2; zify_cond K2.
      + apply KEXIT.
      + apply (walkB e3 o (o + l)); try assumption; [lia| exists be; split; [exact Hbe| exact NBE]|].
        intros t' bt' g17 HT' HBT NBT. apply (KOK t' bt'); [lia| exact HBT| exact NBT]. }
  chkbN 13 (A + e3) SHWT kk SHRk Hk.
  destruct Hk as [-> | [G1 G2]].
  - step. step. lit_branch. apply CONT.
  - step. rewrite (sxb_small kk) by lia.
    step. if_cases G3; zify_cond G3; [| exfalso; lia].
    zstep.
    step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
    apply CONT.
Qed.

#[using="HC FI lo st F FL SF BN"] Lemma runsP : forall (o l : Z) (s rr : list byte) (bcr : byte),
  0 <= o -> 0 <= l -> o + l < bn ->
  skipn (Z.to_nat o) (set_byte bs (Z.to_nat (o + l)) zb) = s ++ zb :: rr -> ~ In zb s ->
  nth_error bs (Z.to_nat (o + l)) = Some bcr -> (bv_unsigned bcr = 13 \/ bv_unsigned bcr = 10) ->
  sscanf_model ScanInt.FMT_STATUSLINE (map bv_unsigned (skipn (Z.to_nat o) (set_byte bs (Z.to_nat (o + l)) zb) ++ sl)) (Prelim.zlength (map bv_unsigned s)) = Some 3 ->
  exists j1 e1 j2 e2 j3 e3, P0.H_presp_A.runs3 bs o j1 e1 j2 e2 j3 e3 /\ e3 <= o + l.
Proof.
  intros o l s rr bcr O0 L0 KN SPLIT NIN Hbcr CRLF SM.
  assert (LBSn : length bs = Z.to_nat bn) by (clear - BN; lia).
  assert (Htxt : map bv_unsigned (skipn (Z.to_nat o) (set_byte bs (Z.to_nat (o + l)) zb) ++ sl) = map bv_unsigned s ++ 0 :: map bv_unsigned (rr ++ sl)).
  { rewrite SPLIT, <- app_assoc. cbn [app]. rewrite map_app. cbn [map]. replace (bv_unsigned zb) with 0%Z by (vm_compute; reflexivity). reflexivity. }
  assert (NZ : Forall (fun c => 0 < c < 256) (map bv_unsigned s)).
  { apply Forall_map. apply Forall_forall. intros bb Hbb. cbv beta. pose proof (P0.H_presp_A.byte_range bb) as R.
    assert (bb <> zb) by (intros ->; exact (NIN Hbb)). enough (bv_unsigned bb <> 0)%Z by lia.
    intros E. apply H. apply bv_eq. rewrite E. vm_compute. reflexivity. }
  rewrite Htxt in SM.
  destruct (sscanf_model_scan_count ScanInt.FMT_STATUSLINE (map bv_unsigned s) (map bv_unsigned (rr ++ sl)) 3 NZ sd_ok_status SM) as [SC3|[X _]]; [| lia].
  symmetry in SC3. destruct (statusline_runs (map bv_unsigned s) SC3) as (j1 & e1 & j2 & e2 & j3 & e3 & RRS).
  destruct (P0.H_presp_B.runs_bridge bs o l s rr bcr j1 e1 j2 e2 j3 e3 O0 L0 ltac:(lia) SPLIT NIN Hbcr CRLF RRS) as [RUNS E3L].
  exists (o + Z.of_nat j1), (o + Z.of_nat e1), (o + Z.of_nat j2), (o + Z.of_nat e2), (o + Z.of_nat j3), (o + Z.of_nat e3).
  split; [exact RUNS| lia].
Qed.

Definition WEP : list ivl := [(lo, q); (F, F + 64); (SF, SF + 8); (FL, FL + 1)]%Z.
#[using="bs sl m0 RF0 PLB"] Lemma sub_fp_WEP : sub_fp WEP W0.
Proof.
  pose proof geomP as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  intros x Hx. unfold WEP. cbn [outside] in *. destruct Hx as (H1 & H2 & H3 & _).
  split; [exact H1|]. split; [clear - H2 GF1 GF2; lia|]. split; [clear - H3 ESF ESHB EKF EKB GF1 GF2; lia|]. split; [clear - H2 GF4 GF5; lia| exact I].
Qed.
Definition rframeP (R : mem -> Prop) : Prop := forall m m', R m -> munch WEP m m' -> wmono asegs m m' -> R m'.

Definition postB (mb : mem) (X : Z -> mem -> Prop) : machine_state -> Prop :=
  fun ms' => exists (r : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (st' : fsstate FI),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F_ (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch W0 mb m' /\ wmono asegs mb m' /\ mem_inv asegs m'
    /\ fkeep FI WP st mb m' /\ fs_live FI st' = fs_live FI st /\ RFAKE FI st' m'
    /\ stk asegs m' lo q /\ asan_env asegs m'
    /\ X r m'.

#[using="kq bs sl m0 CLO LO AL16 RF0 PLB"] Lemma exitP : forall (mb : mem) (r : Z) (X : Z -> mem -> Prop) q' m tyw tw1 tw2 lb ll x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x27 x28 x29 x30 x31,
  minvB mb q' m tyw tw1 tw2 lb ll -> X r m -> rframeP (X r) ->
  evt asegs (postB mb X) (LSTP 0x88094 q' x1 x5 x6 x7 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV HX RFR.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j24 & j4 & QC) & TYC & TC & GAP & FRhi & FH & LINE & (j8 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomP as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  destruct (new_frame_facts FI st 0 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & _).
  pose proof (new_frame_fk FI st 0 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
  destruct (liveP stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  clear PFAP PFS1 PFS2. hideW0 MU WM.
  pose proof (munch_refl WEP m) as MUE. pose proof (wmono_refl asegs m) as WME. unfold WEP in MUE.
  pose proof (munch_refl [(lo, q); (F, F + 64); (SF, SF + 8)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  step.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(SF, SF + 8)]%Z mm) as MUs; pose proof (wmono_refl asegs mm) as WMs end.
  hide_mem_except SHF. unhide MUs. unhide WMs.
  sstep. sstep.
  unhide_transport MUs WMs. clear MUs WMs.
  step. step. step; fix_lit_store.
  step.   if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(SF, SF + 8)]%Z mm) as MUs; pose proof (wmono_refl asegs mm) as WMs end.
  hide_mem_except SHF. unhide MUs. unhide WMs.
  do 8 sstep.
  unhide_transport MUs WMs. clear MUs WMs.
  step.

  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(FL, FL + 1)]%Z mm) as MU0; pose proof (wmono_refl asegs mm) as WM0 end.
  sstep.
  env_sync AE MU0 WM0. fk_sync FI RF MU0 FK LSUB.

  join_chunks LINE FT FRt. join_chunks FH FRt FRF.
  lazymatch type of RF with RFAKE _ ?st2 ?mb2 =>
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (SHF' : rw_cells asegs mc (sh (ff_addr (fs_newff FI st 0))) (shadow_cells (repeat 245 (Z.to_nat (ff_shsize (fs_newff FI st 0))))))
      by (change (ff_addr (fs_newff FI st 0)) with F; change (sh F) with SF; unfold ff_shsize; rewrite FCLS; exact SHF);
    destruct (release FI st2 (fs_newff FI st 0) (fs_live FI st) mb2 mc _ RF LIVE1 MU0 WM0 FLG SHF' FRF
                ltac:(unfold ff_size; rewrite FCLS; reflexivity)) as [RF3 LIVE3]
  end end.
  clear RF MU0 WM0 SHF'.
  step.   step.
  do 13 step.
  step.   step.

  release_frame QC ST (q' + 36)%Z. release_frame TYC ST (q' + 40)%Z. release_frame TC ST (q' + 56)%Z.
  pose proof (stk_merge asegs _ _ _ _ ST GAP ltac:(lia)) as STm. clear ST GAP.
  release_frame FRhi STm q.
  absorbW0 MU WM MUE WME sub_fp_WEP.
  apply evt_done. unfold postB. exists r. do 14 eexists.
  lazymatch goal with |- exists _ _, MS _ _ _ _ _ ?mm _ = _ /\ _ => exists mm, (fs_after_release FI stc) end.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FK|]. split; [exact LIVE3|]. split; [exact RF3|].
  split; [exact STm|]. split; [exact AE|]. exact (RFR m _ HX MUE WME).
Qed.

#[using="bs sl m0 CLO RF0 PHI PLB"] Lemma WEP_dj_P : forall X n, P <= X -> X + n <= P + 504 -> disjoint_from WEP X n.
Proof.
  intros X n H1 H2. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomP as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  unfold WEP. cbn [disjoint_from].
  split; [left; clear - H2 PHI CLO; lia|]. split; [clear - H1 H2 PFAP; lia|].
  split; [clear - H1 H2 ESF EKF GF1 GF2 PFS1 PFS2 FSB1 FSB2 FSB5 ACR; lia|]. split; [right; clear - H1 GF5 PFS1; lia| exact I].
Qed.
#[using="P bs m0 CLO RF0 PLB AFS ABAND SL7 SLHI"] Lemma WEP_dj_T : forall X n, A <= X -> X + n <= A + bn + Z.of_nat (length sl) -> disjoint_from WEP X n.
Proof.
  intros X n H1 H2. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomP as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  pose proof ABAND as ABu. unfold ABANDd in ABu.
  unfold WEP. cbn [disjoint_from].
  split; [left; clear - H2 SLHI CLO; lia|].
  split; [clear - H1 H2 AFS SL7 SLAL EKB GF1 GF2; lia|].
  split; [clear - H1 H2 ABu SL7 ESF EKF GF1 GF2 FSB1 FSB2 ACR; lia|].
  split; [clear - H1 H2 AFS SL7 SLAL EKB GF4 GF5; lia| exact I].
Qed.

#[using="P bs sl m0 CLO RF0 PLB"] Lemma WEP_dj_E : disjoint_from WEP ERRNO_A 4.
Proof.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomP as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  unfold WEP. cbn [disjoint_from]. repeat (split; [clear - CLO ACR ESF EKF GF1 GF4 FSB1; lia|]). exact I.
Qed.

#[using="bs sl m0 CLO RF0 PHI PLB"] Lemma rinvP_rframe : forall sc maj min, rframeP (fun m => rinvP m sc maj min).
Proof.
  intros sc maj min m m' (RSC & SMC & VERC & CTLC & (ev & ERRC)) MU WM. unfold rinvP.
  split; [apply (rw_cells_transport asegs WEP m m' _ _ RSC MU WM); apply WEP_dj_P; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  split; [apply (rw_cells_transport asegs WEP m m' _ _ SMC MU WM); apply WEP_dj_P; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  split; [apply (rw_cells_transport asegs WEP m m' _ _ VERC MU WM); apply WEP_dj_P; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  split; [apply (rw_cells_transport asegs WEP m m' _ _ CTLC MU WM); apply WEP_dj_P; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  exists ev. apply (rw_cells_transport asegs WEP m m' _ _ ERRC MU WM). apply WEP_dj_E.
Qed.
#[using="m0 CLO RF0 BN PHI PLB AFS ABAND SL7 SLHI"] Lemma pinvP_rframe : forall cur sc maj min, rframeP (fun m => pinvP m cur sc maj min).
Proof.
  intros cur sc maj min m m' (SC & MBC & TXC & SLK & RV) MU WM. unfold pinvP.
  split; [apply (rw_cells_transport asegs WEP m m' _ _ SC MU WM); apply WEP_dj_P; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  split; [apply (rw_cells_transport asegs WEP m m' _ _ MBC MU WM); apply WEP_dj_P; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  split; [apply (rw_cells_transport asegs WEP m m' _ _ TXC MU WM); apply WEP_dj_T; cbn [cells_size csize Nat.add]; [lia| rewrite Nat.add_0_r, Z2Nat.id by (clear - BN; lia); lia]|].
  split; [apply (bytes_at_transport asegs WEP m m' _ _ SLK MU); apply WEP_dj_T; lia|].
  exact (rinvP_rframe sc maj min m m' RV MU WM).
Qed.

#[using="kE CLO RF0 F FL SF BN PLB AFS ABAND SL7 SLHI SLAL"] Lemma pinvP_pro : forall m cur sc maj min,
  pinvP m0 cur sc maj min -> munch ((lo, q) :: FSIV [])%Z m0 m -> wmono asegs m0 m -> fkeep FI [] st m0 m -> pinvP m cur sc maj min.
Proof.
  intros m cur sc maj min (SC & MBC & TXC & SLK & (RSC & SMC & VERC & CTLC & (ev & ERRC))) MU WM FK.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomP as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  pose proof ABAND as ABu. unfold ABANDd in ABu.
  assert (PL : forall X n, P <= X -> X + n <= P + 504 -> in_live FI st X n) by (intros X n H1 H2; left; apply (lb_sub _ P 504 X n PLB); lia).
  assert (DJT : forall X n, A <= X -> X + n <= A + bn + Z.of_nat (length sl) -> disjoint_from ((lo, q) :: FSIV [])%Z X n).
  { intros X n H1 H2. cbn [disjoint_from]. split; [left; clear - H2 SLHI CLO; lia|].
    split; [clear - H1 H2 AFS SL7 SLAL EKB; lia|]. split; [| exact I].
    clear - H1 H2 ABu SL7 ESHB EKB FSB1 FSB2 ACR. lia. }
  unfold pinvP, rinvP.
  split; [apply (rw_cells_fkeep FI [] st m0 m _ _ SC FK WM); [apply PL; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia| exact I]|].
  split; [apply (rw_cells_fkeep FI [] st m0 m _ _ MBC FK WM); [apply PL; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia| exact I]|].
  split; [apply (rw_cells_transport asegs _ m0 m _ _ TXC MU WM); apply DJT; cbn [cells_size csize Nat.add]; [lia| rewrite Nat.add_0_r, Z2Nat.id by (clear - BN; lia); lia]|].
  split; [apply (bytes_at_transport asegs _ m0 m _ _ SLK MU); apply DJT; lia|].
  split; [apply (rw_cells_fkeep FI [] st m0 m _ _ RSC FK WM); [apply PL; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia| exact I]|].
  split; [apply (rw_cells_fkeep FI [] st m0 m _ _ SMC FK WM); [apply PL; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia| exact I]|].
  split; [apply (rw_cells_fkeep FI [] st m0 m _ _ VERC FK WM); [apply PL; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia| exact I]|].
  split; [apply (rw_cells_fkeep FI [] st m0 m _ _ CTLC FK WM); [apply PL; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia| exact I]|].
  exists ev. apply (rw_cells_transport asegs _ m0 m _ _ ERRC MU WM).
  cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
  repeat (split; [clear - CLO ACR FSB1 FSB2 ESHB EKB; lia|]). exact I.
Qed.

Definition XEP (cur : Z) : Z -> mem -> Prop := fun r m' => exists cur' sc' maj' min',
  pinvP m' cur' sc' maj' min' /\ r <> 4 /\ 0 <= r <= 5 /\ cur <= cur' <= len
  /\ - 2^31 <= sc' < 2^31 /\ - 2^31 <= maj' < 2^31 /\ - 2^31 <= min' < 2^31.
#[using="m0 CLO RF0 BN PHI PLB AFS ABAND SL7 SLHI"] Lemma XEP_rframe : forall cur r, rframeP (XEP cur r).
Proof.
  intros cur r ma mb (c & s' & ma' & mi' & PV & REST) MUx WMx. exists c, s', ma', mi'.
  split; [exact (pinvP_rframe c s' ma' mi' ma mb PV MUx WMx)| exact REST].
Qed.

Definition callstP (q' t' n : Z) (bcr x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m : mem) : machine_state :=
  MS (mkR (Z_to_bv 64 0x8804c) (Z_to_bv 64 q') gp tp x5 x6 x7 (Z_to_bv 64 q) (Z_to_bv 64 q') (Z_to_bv 64 (P + 232)) (Z_to_bv 64 (A + t')) (Z_to_bv 64 n)
          x13 x14 x15 x16 x17 (Z_to_bv 64 F) (Z_to_bv 64 P) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 (P + 228)) (Z_to_bv 64 (P + 280)) (Z_to_bv 64 (P + 276))
          (Z_to_bv 64 F) (Z_to_bv 64 SF) (Z_to_bv 64 2147450880) bcr x28 x29 x30 x31)
     F_ (Z_to_bv 64 0x8ca3c) fc None m (seg_rom asegs).

Definition midP (cur : Z) : machine_state -> Prop := fun ms =>
  postB m0 (XEP cur) ms
  \/ (exists q' t' o l cur' sc' maj' min' tyw tw1 tw2 (bcr x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m,
        ms = callstP q' t' (l - (t' - o)) bcr x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m
        /\ minvP q' m tyw tw1 tw2 (Z_to_bv 64 (A + o)) (Z_to_bv 64 l) /\ pinvP m cur' sc' maj' min'
        /\ 0 <= o /\ o <= t' /\ t' <= o + l /\ o + l < cur' /\ cur' <= len /\ cur <= cur'
        /\ 0 <= sc' < 2^31 /\ 0 <= maj' < 2^31 /\ 0 <= min' < 2^31).

#[using="IC STACK_MALLOC_0 STACK_MALLOC_1 kq kP kE CLO LO AL16 QHI RF0 FCO FE0 st1 BN LBS BNMAX CAP AHI SHWPo PLO PHI PAL PLB SHWA ALO AIMG ABHI AFS ABAND SL7 SLHI SLAL SHWSEP SHWFMT SHZ SHR Q47 SHWFMT2 TPV canary SSPG SSPC"] Lemma frontP : forall (cur sc maj min : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
  stk asegs m0 lo q -> mem_inv asegs m0 -> asan_env asegs m0 -> pinvP m0 cur sc maj min -> 0 <= cur <= len ->
  - 2^31 <= sc < 2^31 -> - 2^31 <= maj < 2^31 -> - 2^31 <= min < 2^31 ->
  evt asegs (midP cur)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (Z_to_bv 64 presp_entryA) fc None m0 (seg_rom asegs)).
Proof.
  intros cur sc maj min t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ST MI AE PINV HCUR SR MR NR.
  assert (KX : forall r cur' sc' maj' min' q' m tyw tw1 tw2 lb ll x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x27 x28 x29 x30 x31,
             (r <> 4 /\ 0 <= r <= 5) -> cur <= cur' <= len -> - 2^31 <= sc' < 2^31 -> - 2^31 <= maj' < 2^31 -> - 2^31 <= min' < 2^31 ->
             minvP q' m tyw tw1 tw2 lb ll -> pinvP m cur' sc' maj' min' ->
             evt asegs (midP cur) (LSTP 0x88094 q' x1 x5 x6 x7 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 m)).
  { intros r cur' sc' maj' min' q' m tyw tw1 tw2 lb ll x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 RN CR S1 S2 S3 MV PV.
    eapply evt_mono; [apply (exitP m0 r (XEP cur) q' m tyw tw1 tw2 lb ll); [exact MV| | apply XEP_rframe]| intros ms' H; left; exact H].
    exists cur', sc', maj', min'. split; [exact PV|]. split; [exact (proj1 RN)|]. split; [exact (proj2 RN)|]. split; [exact CR|]. split; [exact S1|]. split; [exact S2| exact S3]. }
  apply (prologueP t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ST MI AE).
  intros q' m tyw tw1 tw2 lb ll x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 MV MUP FKP.
  assert (PV : pinvP m cur sc maj min).
  { destruct MV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WM & _). exact (pinvP_pro m cur sc maj min PINV MUP WM FKP). }
  pose proof (fsenv_FSIV FI [] lo q m0 m FE0 MUP CLO (Forall_nil _)) as FEm.
  clear MUP FKP.
  apply (tokloopP (Datatypes.S (Z.to_nat (len - cur))) cur sc maj min q' m tyw tw1 tw2 lb ll); [lia| exact HCUR| exact MV| exact PV| exact FEm| |].
  { intros r cur' m' tyw' tw1' tw2' y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 RN CR MV' PV'.
    apply (KX r cur' sc maj min q' m' tyw' tw1' tw2' lb ll); assumption. }
  intros cur1 tlz ty m1 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 C1 T1 T2 T3 T4 T5 MV1 PV1 FE1.
  apply (pbmatchP cur1 tlz ty sc maj min q' m1 lb ll); [lia| exact T1| exact T2| exact MV1| exact PV1| exact FE1| |].
  { intros r cur' m' tyw' tw1' tw2' lb' ll' z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 RN CR MV' PV'.
    apply (KX r cur' sc maj min q' m' tyw' tw1' tw2' lb' ll'); try assumption. lia. }
  intros cur' o l m2 tyw2 tw12 tw22 z1 z5 z6 z7 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 O1 L0 OL CL (bcr & Hbcr & CRLF) MV2 PV2.
  apply (nulP o l cur' sc maj min bcr q' m2 tyw2 tw12 tw22); [lia| exact L0| exact OL| exact CL| exact Hbcr| exact MV2| exact PV2|].
  intros m3 u11 u12 u13 MV3 PW3.
  apply (scanfP o l cur' sc maj min q' m3 tyw2 tw12 tw22); [lia| exact L0| exact OL| exact CL| exact MV3| exact PW3|].
  intros r v1 v2 v3 s rr m4 w1 w5 w6 w7 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 SPLIT NIN SM RR MV4 PW4.
  pose proof (P0.H_presp_B.s32v_range v1) as R1. pose proof (P0.H_presp_B.s32v_range v2) as R2. pose proof (P0.H_presp_B.s32v_range v3) as R3.
  apply (restoreP o l cur' (P0.H_presp_B.s32v v3) (P0.H_presp_B.s32v v1) (P0.H_presp_B.s32v v2) r bcr q' m4 tyw2 tw12 tw22); [lia| exact L0| exact OL| exact CL| exact Hbcr| exact RR| exact MV4| exact PW4| |].
  { intros m5 u11' u12' u13' u14' RN3 MV5 PV5.
    apply (KX 3 cur' (P0.H_presp_B.s32v v3) (P0.H_presp_B.s32v v1) (P0.H_presp_B.s32v v2) q' m5 tyw2 tw12 tw22 (Z_to_bv 64 (A + o)) (Z_to_bv 64 l)); try assumption; lia. }
  intros m5 u11' u12' u13' u14' RE3 MV5 PV5. subst r.
  apply (signsP cur' (P0.H_presp_B.s32v v3) (P0.H_presp_B.s32v v1) (P0.H_presp_B.s32v v2) q' m5 tyw2 tw12 tw22 (Z_to_bv 64 (A + o)) (Z_to_bv 64 l)); [exact R3| exact R1| exact R2| exact MV5| exact PV5| |].
  { intros u11'' NEG.
    apply (KX 3 cur' (P0.H_presp_B.s32v v3) (P0.H_presp_B.s32v v1) (P0.H_presp_B.s32v v2) q' m5 tyw2 tw12 tw22 (Z_to_bv 64 (A + o)) (Z_to_bv 64 l)); try assumption; lia. }
  intros u11'' POS1 POS2 POS3.
  destruct (runsP o l s rr bcr ltac:(lia) L0 ltac:(clear - OL CL LBS; lia) SPLIT NIN Hbcr CRLF SM) as (j1 & e1 & j2 & e2 & j3 & e3 & RUNS & E3L).
  pose proof MV5 as MV5'. pose proof PV5 as PV5'.
  destruct MV5' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & LINE5 & _ & _ & _ & MI5 & MU5 & _).
  destruct PV5' as (_ & _ & TXC5 & _).
  assert (NBL : ~ P0.H_presp_A.bblank bcr) by (unfold P0.H_presp_A.bblank; clear - CRLF; lia).
  apply (walkP o l j1 e1 j2 e2 j3 e3 bcr q' m5); [exact RUNS| exact E3L| lia| exact Hbcr| exact NBL| exact MI5| exact (text_bytes _ TXC5)
    | apply (shw_frame_fs FI W0 m0 m5 A len (SHWA ltac:(lia)) MU5 W0_fsw); clear - AFS LBS; lia| exact LINE5| |].
  { intros v5 v11 v12 v13 v14 v15 v16 v17.
    apply (KX 3 cur' (P0.H_presp_B.s32v v3) (P0.H_presp_B.s32v v1) (P0.H_presp_B.s32v v2) q' m5 tyw2 tw12 tw22 (Z_to_bv 64 (A + o)) (Z_to_bv 64 l)); try assumption; lia. }
  intros t' bt' v5 v17 T'R Hbt' NBT.

  pose proof MV5 as MV5'.
  destruct MV5' as ((kq' & Hq32) & Hq & ST5 & (j24 & j4 & QC) & TYC & TC & GAP & FRhi & FH & LINE & (j8 & FT) & SHF & FLG & MI5' & MU5' & WM5 & FK5 & AE5 & (stc & RF5 & LIVE5)).
  pose proof (proj1 RUNS) as ORD.
  step. step.
  zstep.
  replace (Z_to_bv 64 (A + o + l - (A + t'))) with (Z_to_bv 64 (l - (t' - o))) by (f_equal; lia).
  step. step.
  apply evt_done. right.
  exists q', t', o, l, cur', (P0.H_presp_B.s32v v3), (P0.H_presp_B.s32v v1), (P0.H_presp_B.s32v v2), tyw2, tw12, tw22.
  do 13 eexists. exists m5.
  split; [reflexivity|]. split; [exact MV5|]. split; [exact PV5|].
  repeat (split; [lia|]). lia.
Qed.

Definition WLP : list ivl := ((P + 448, P + 452) :: WEP)%Z.
Definition rframeL (R : mem -> Prop) : Prop := forall m m', R m -> munch WLP m m' -> wmono asegs m m' -> R m'.
Definition ctlP (m : mem) (pos' : Z) : Prop :=
  rw_cells asegs m (P + 440) [C4 (wz err); C4 (wz hack); C4 (wz pos'); C4 (wz entp); C4 (wz clen); C4 (wz 0); C8 (wz csz); C8 (wz esp)].

#[using="kq kP bs sl m0 CLO LO AL16 RF0 PLO PHI PAL PLB"] Lemma lateP : forall (mb : mem) (R : mem -> Prop) q' m tyw tw1 tw2 lb ll x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x27 x28 x29 x30 x31,
  minvB mb q' m tyw tw1 tw2 lb ll -> ctlP m pos -> shw m P 504 -> R m -> rframeL R ->
  evt asegs (postB mb (fun r m' => r = 4 /\ ctlP m' 2 /\ R m'))
    (LSTP 0x8804c q' x1 x5 x6 x7 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x27 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV CTLC SHWP HR RFL. unfold ctlP in CTLC.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j24 & j4 & QC) & TYC & TC & GAP & FRhi & FH & LINE & (j8 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomP as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  pose proof (munch_refl WLP m) as MUL. pose proof (wmono_refl asegs m) as WML. unfold WLP, WEP in MUL.
  pose proof (munch_refl [(P + 448, P + 452)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  step.   lit_branch.
  step. step. step.
  chk8N 11 (P + 448) SHWP. step. lit_branch.
  step.
  step; fix_lit_store.
  step.
  destruct (liveP stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  clear LVF LVS LVL PLB1 LSUB.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply (exitP mb 4 (fun r m' => r = 4 /\ ctlP m' 2 /\ R m') q' mm tyw tw1 tw2 lb ll);
    [ mv_tacP
    | split; [reflexivity|]; split; [exact CTLC| exact (RFL m mm HR MUL WML)]
    | ] end.
  intros ma mb' (E4 & CT & HRa) MUx WMx. split; [exact E4|]. split.
  - unfold ctlP in *. apply (rw_cells_transport asegs WEP ma mb' _ _ CT MUx WMx). apply WEP_dj_P; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
  - apply (RFL ma mb' HRa); [| exact WMx]. eapply (munch_weaken WEP WLP); [| exact MUx]. intros x Hx. unfold WLP in Hx. cbn [outside] in Hx. exact (proj2 Hx).
Qed.

Variable AI : am_if FI.
Local Notation BLa := (list (AllocIF.block (am_K FI AI))).

#[using="bs sl m0 CLO LO RF0 PHI PLB"] Lemma minvB_apx : forall (LB : BLa) (mb : mem) q' m1 m2 tyw tw1 tw2 lb ll (stc : fsstate FI),
  minvB mb q' m1 tyw tw1 tw2 lb ll -> apx FI AI [(P + 232, P + 264)]%Z LB q' m1 m2 ->
  stk asegs m2 lo q' -> mem_inv asegs m2 -> asan_env asegs m2 ->
  RFAKE FI stc m2 -> fs_live FI stc = fs_newff FI st 0 :: fs_live FI st ->
  minvB m2 q' m2 tyw tw1 tw2 lb ll.
Proof.
  intros LB mb q' m1 m2 tyw tw1 tw2 lb ll stc INV AP ST2 MI2 AE2 RF2 LIVE2.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j24 & j4 & QC) & TYC & TC & GAP & FRhi & FH & LINE & (j8 & FT) & SHF & FLG & MI & MU & WM & FK & AE & _).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomP as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  assert (TS : forall X cs, rw_cells asegs m1 X cs -> q' <= X -> rw_cells asegs m2 X cs).
  { intros X cs H HX. apply (apx_rw_cells FI AI _ LB q' m1 m2 X cs AP H); [apply aclient_range_above; exact HX|].
    cbn [disjoint_from]. split; [right; clear - HX Hq LO CLO PHI; lia| exact I]. }
  assert (TF : forall X cs, rw_cells asegs m1 X cs -> FSB FI <= X -> X + Z.of_nat (cells_size cs) <= FSB FI + A0_FS_SIZE ->
               (X + Z.of_nat (cells_size cs) <= P + 232 \/ P + 264 <= X) -> rw_cells asegs m2 X cs).
  { intros X cs H H1 H2 H3. apply (apx_rw_cells FI AI _ LB q' m1 m2 X cs AP H); [apply aclient_range_fs; [exact H1| exact H2]|].
    cbn [disjoint_from]. split; [exact H3| exact I]. }
  apply TS in QC; [| lia]. apply TS in TYC; [| lia]. apply TS in TC; [| lia]. apply TS in FRhi; [| lia].
  apply TF in FH; [| lia| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
  apply TF in LINE; [| lia| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
  apply TF in FT; [| lia| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
  apply TF in FLG; [| lia| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
  apply (apx_rw_cells FI AI _ LB q' m1 m2 _ _ AP) in SHF;
    [| apply aclient_range_fs_shadow; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - ESF ESHB EKF EKB GF1 GF2; lia
     | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; split; [clear - ESF EKF GF1 GF2 PFS1 PFS2 FSB1 FSB2 FSB5 ACR; lia| exact I]].
  assert (GAP2 : stk asegs m2 (q' + 56) (q + -104)).
  { eapply (stk_gagree (fun a => aclient FI AI LB q' a /\ outside [(P + 232, P + 264)]%Z a)); [intros a Ha [Hc Ho]; exact (AP a Ha Hc Ho)| exact GAP|].
    intros a Ha. split; [left; lia|]. cbn [outside]. split; [clear - Ha Hq LO CLO PHI; lia| exact I]. }
  clear ST GAP MI MU WM FK AE AP.
  pose proof (munch_refl W0 m2) as MU2. pose proof (wmono_refl asegs m2) as WM2. pose proof (fkeep_refl FI WP st m2) as FK2.
  unfold minvB. split; [eexists; eassumption|]. split; [assumption|].
  repeat (split; [first [eassumption | (eexists; eassumption) | (eexists; eexists; eassumption)] |]). exists stc. split; assumption.
Qed.

Definition lateR (m : mem) (cur sc maj min : Z) : Prop :=
  rw_cells asegs m (P + 480) [C8 (wz (P + 400)); C8 (wz cur); C4 (wz 0)]
  /\ rw_cells asegs m (P + 400) [C8 (wz A); C8 (wz len); C8 (wz cap); C8 (wz 5)]
  /\ rw_cells asegs m A [CB (Z.to_nat bn) bs]
  /\ rw_cells asegs m (P + 224) [C4 (wz rm); C4 (wz sc)]
  /\ rw_cells asegs m (P + 264) [C8 (wz 0); C4 (wz isreq); C4 (wz maj); C4 (wz min); C4 pad]
  /\ (exists ev, rw_cells asegs m ERRNO_A [C4 ev]).

#[using="lo st m0 RF0 F FL SF BN PLB AFS"] Lemma pinv_apx : forall (LB : BLa) q' m1 m2 cur sc maj min,
  pinvP m1 cur sc maj min -> apx FI AI [(P + 232, P + 264)]%Z LB q' m1 m2 ->
  aclient_range FI AI LB q' A bn -> aclient_range FI AI LB q' ERRNO_A 4 ->
  lateR m2 cur sc maj min /\ ctlP m2 pos.
Proof.
  intros LB q' m1 m2 cur sc maj min (SC & MBC & TXC & SLK & (RSC & SMC & VERC & CTLC & (ev & ERRC))) AP ACT ACE.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomP as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  assert (TF : forall X cs, rw_cells asegs m1 X cs -> P <= X -> X + Z.of_nat (cells_size cs) <= P + 504 ->
               (X + Z.of_nat (cells_size cs) <= P + 232 \/ P + 264 <= X) -> rw_cells asegs m2 X cs).
  { intros X cs H H1 H2 H3. apply (apx_rw_cells FI AI _ LB q' m1 m2 X cs AP H); [apply aclient_range_fs; lia|].
    cbn [disjoint_from]. split; [exact H3| exact I]. }
  apply TF in SC; [| lia| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
  apply TF in MBC; [| lia| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
  apply TF in RSC; [| lia| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
  apply TF in VERC; [| lia| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
  apply TF in CTLC; [| lia| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
  apply (apx_rw_cells FI AI _ LB q' m1 m2 _ _ AP) in TXC;
    [| cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear - BN; lia); exact ACT
     | cbn [disjoint_from cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear - BN; lia); split; [clear - AFS PFS1 PFS2 LBS BN; lia| exact I]].
  apply (apx_rw_cells FI AI _ LB q' m1 m2 _ _ AP) in ERRC;
    [| exact ACE | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; split; [clear - PFS1 FSB1; lia| exact I]].
  split; [| exact CTLC]. unfold lateR. repeat (split; [assumption|]). exists ev. exact ERRC.
Qed.

#[using="bs sl m0 CLO RF0 PHI PLB"] Lemma WLP_dj_P : forall X n, P <= X -> X + n <= P + 504 -> (X + n <= P + 448 \/ P + 452 <= X) -> disjoint_from WLP X n.
Proof. intros X n H1 H2 H3. unfold WLP. cbn [disjoint_from]. split; [exact H3| exact (WEP_dj_P X n H1 H2)]. Qed.
#[using="bs sl m0 CLO RF0 PLB"] Lemma WLP_dj_out : forall X n, 0 <= n -> X + n <= alloc_ceiling -> (X + n <= FSB FI \/ FSB FI + A0_FS_SIZE <= X) ->
  (X + n <= 0x7fff7000 \/ 0x10007fff8000 <= X) -> disjoint_from WLP X n.
Proof.
  intros X n H0 H1 H2 H3. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomP as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  unfold WLP, WEP. cbn [disjoint_from].
  split; [clear - H0 H2 PFS1 PFS2; lia|]. split; [left; clear - H1 CLO; lia|]. split; [clear - H0 H2 GF1 GF2; lia|].
  split; [clear - H0 H3 ESF EKF GF1 GF2 FSB1 FSB2 ACR; lia|]. split; [clear - H0 H2 GF4 GF5; lia| exact I].
Qed.
#[using="sl m0 CLO RF0 BN PHI PLB ABHI AFS ABAND"] Lemma lateR_rframe : forall cur sc maj min, rframeL (fun m => lateR m cur sc maj min).
Proof.
  intros cur sc maj min m m' (SC & MBC & TXC & RSC & VERC & (ev & ERRC)) MU WM. unfold lateR.
  pose proof ABAND as ABu. unfold ABANDd in ABu.
  split; [apply (rw_cells_transport asegs WLP m m' _ _ SC MU WM); apply WLP_dj_P; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  split; [apply (rw_cells_transport asegs WLP m m' _ _ MBC MU WM); apply WLP_dj_P; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  split; [apply (rw_cells_transport asegs WLP m m' _ _ TXC MU WM); cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear - BN; lia);
          apply WLP_dj_out; [clear - BN; lia| exact ABHI| exact AFS| clear - ABu; lia]|].
  split; [apply (rw_cells_transport asegs WLP m m' _ _ RSC MU WM); apply WLP_dj_P; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  split; [apply (rw_cells_transport asegs WLP m m' _ _ VERC MU WM); apply WLP_dj_P; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  exists ev. apply (rw_cells_transport asegs WLP m m' _ _ ERRC MU WM). unfold WLP. cbn [disjoint_from]. split; [| exact WEP_dj_E].
  pose proof geomP as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5). left. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - PFS1 FSB1. lia.
Qed.

End W.

