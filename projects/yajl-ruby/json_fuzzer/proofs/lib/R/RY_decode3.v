(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel SFW1_lemmas InitMem Arr Mem NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMallocTree RMalloc_iface RYajlRep RYajl_iface RY_lib RY_rz RY_kit2 RF_strlen.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase YajlBuf YajlLex YajlDecode YajlLeaf YajlFactsBuf YajlFactsLex YajlFactsDecode YajlFactsBits.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_secinst.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Export RY_decode2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma zbytes_firstn : forall k l, zbytes (firstn k l) = firstn k (zbytes l).
Proof. intros k l. unfold zbytes. rewrite firstn_map. reflexivity. Qed.
Lemma zbytes_skipn : forall k l, zbytes (skipn k l) = skipn k (zbytes l).
Proof. intros k l. unfold zbytes. rewrite skipn_map. reflexivity. Qed.

Lemma bytes_at_sub : forall m A bs i k,
  bytes_at rsegs m A bs -> (i <= length bs)%nat -> bytes_at rsegs m (A + Z.of_nat i) (firstn k (skipn i bs)).
Proof.
  intros m A bs i k HB Hi.
  rewrite <- (firstn_skipn i bs) in HB. apply bytes_at_app in HB. destruct HB as [_ HB].
  rewrite length_firstn, Nat.min_l in HB by lia.
  rewrite <- (firstn_skipn k (skipn i bs)) in HB. apply bytes_at_app in HB. destruct HB as [HB _]. exact HB.
Qed.

Lemma bytes_at_zslice : forall m A str i k,
  bytes_at rsegs m A (zbytes str) -> 0 <= i <= zlength str -> bytes_at rsegs m (A + i) (zbytes (zslice str i k)).
Proof.
  intros m A str i k HB Hi. unfold zslice. rewrite zbytes_firstn, zbytes_skipn.
  replace i with (Z.of_nat (Z.to_nat i)) at 1 by lia. apply bytes_at_sub; [exact HB|]. rewrite zbytes_length. unfold zlength in Hi. lia.
Qed.

Lemma Forall_firstn : forall {A} (P : A -> Prop) k l, Forall P l -> Forall P (firstn k l).
Proof. intros A P k l H. rewrite <- (firstn_skipn k l) in H. apply Forall_app in H. tauto. Qed.
Lemma Forall_skipn : forall {A} (P : A -> Prop) k l, Forall P l -> Forall P (skipn k l).
Proof. intros A P k l H. rewrite <- (firstn_skipn k l) in H. apply Forall_app in H. tauto. Qed.
Lemma Forall_zslice : forall (P : Z -> Prop) str i k, Forall P str -> Forall P (zslice str i k).
Proof. intros P str i k HF. unfold zslice. apply Forall_firstn, Forall_skipn. exact HF. Qed.

(* [comment removed for export] *)
Lemma yzext32_idiom : forall x, 0 <= x < 2^32 ->
  (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) ≪ 32)) ≫ 32) = x.
Proof.
  intros x Hx. rewrite (unsigned_lit x) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite unsigned_lit by (change (2^64) with (2^32 * 2^32); nia).
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.
Lemma yswrap32_small : forall x, -2^31 <= x < 2^31 -> bv_swrap 32 x = x.
Proof. intros x Hx. rewrite ybv_swrap32_eq. rewrite Z.mod_small by lia. lia. Qed.

(* [comment removed for export] *)
End RC__1.
Open Scope yprog_scope.

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section S.
Variable HK : RawAlloc.PState -> list block -> (word -> option byte) -> Model -> Prop.
Hypothesis HKS : HK_silent_stmt HK.
Hypothesis HKP : HK_perm_stmt HK.
Hypothesis HKF : HK_frame_stmt HK.
Hypothesis HKB : HK_blocks_stmt HK.
Hypothesis YAP : ybuf_append_stmt HK.
Hypothesis YHX : yhexToDigit_stmt.

Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia; rewrite ?signed_of_Z by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.
Ltac lkr := repeat match goal with H : LKnil ?l |- _ => unfold LKnil in H end; rewrite ?app_nil_r; repeat match goal with H : ?l = [] |- context [?l] => rewrite H end; cbn [app].
Ltac lk0 := lkr; reflexivity.
(* [comment removed for export] *)
Ltac sb_store := unfold wz; rewrite le1_wz by lia; mem_after_store.
Ltac zle := apply Z.leb_le; vm_compute; reflexivity.
Ltac lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       end).

Section Fn.
Variables (REST : list block) (mbd : mbuf) (db : ybuf) (AF S : Z) (str : list Z) (n lo B : Z) (errv : word) (K : TSet).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
Hypothesis CONT : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : PState)
    (db' : ybuf) (mbd' : mbuf) (LK : list block),
  ystring_decode_rpost HK sp tp m REST mbd db AF S str n lo B errv a0' m' mo' s' db' mbd' LK ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                           F (ret_pc ra) fc None m' (seg_rom rsegs)) mo') K.
Hypothesis K0 : K [].
Hypothesis TP : tp = wz RATP.
Hypothesis CEIL : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RY_DECODE_STACK.
Hypothesis SPB : bv_unsigned sp <= B.
Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
Hypothesis AFIN : yaf_in REST AF.
Hypothesis YR : yroom REST 3.
Hypothesis SF : Forall (fun c => 0 <= c < 256) str.
Hypothesis NL : n = zlength str.
Hypothesis N26 : n < 2^26.
Hypothesis SNZ : S <> 0.
Hypothesis S62 : S + n < 2^62.
Hypothesis TR : (exists bt, In bt REST /\ blk_addr bt <= S /\ S + n <= blk_addr bt + blk_size bt) \/ n = 0.
Hypothesis STXT : 0 < n -> S + n <= alloc_ceiling.
Hypothesis AFC : AF + 32 <= alloc_ceiling.

(* [comment removed for export] *)
#[local] Definition dlits := ltac2:(inst_sec '@RY_decode1.dlits).
#[local] Definition dframe := ltac2:(inst_sec '@RY_decode1.dframe).
#[local] Definition str_pres := ltac2:(inst_sec '@RY_decode1.str_pres).
#[local] Definition dblob := ltac2:(inst_sec '@RY_decode1.dblob).
#[local] Definition dframe_blob := ltac2:(inst_sec '@RY_decode1.dframe_blob).
#[local] Definition decode_exit := ltac2:(inst_sec '@RY_decode1.decode_exit).
#[local] Definition exit_leaf := ltac2:(inst_sec '@RY_decode1.exit_leaf).
#[local] Definition head_ok := ltac2:(inst_sec '@RY_decode1.head_ok).
#[local] Definition decode_lit := ltac2:(inst_sec '@RY_decode1.decode_lit).
#[local] Definition str_read := ltac2:(inst_sec '@RY_decode2.str_read).
#[local] Definition str_byte := ltac2:(inst_sec '@RY_decode2.str_byte).
#[local] Definition decode_uesc := ltac2:(inst_sec '@RY_decode2.decode_uesc).



(* [comment removed for export] *)
Lemma decode_step : forall f', head_ok f' -> head_ok (Datatypes.S f').
Proof.
  intros f' HEAD. unfold head_ok, RY_decode1.head_ok, RY_decode2.head_ok. intros until j88. intros ELK HK1 YS1 FR STK MI AX ERR PRES YAF TB BR BI MBS UB HBE HEN SBX HF HL. apply lk_hide in ELK.
  unfold dframe, RY_decode1.dframe, RY_decode2.dframe, dlits, RY_decode1.dlits, RY_decode2.dlits in FR. cbn [app] in FR.
  unfold wz in *. pose proof LO as LO'. unfold RY_DECODE_STACK, RY_BUF_APPEND_STACK, RY_WRAP_STACK, alloc_ceiling in LO'.
  pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
  unfold RERRNO in ERR. pose proof (zlength_nonneg str) as NL0.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -208)) = bv_unsigned sp + -208) by (apply unsigned_lit; lia).
  pose proof (proj1 TB) as S0.
  destruct AFIN as (hb & HBI & HB1 & HB2).
  pose proof (str_byte e ltac:(lia)) as C0.
  pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl rsegs m1) as WM.
  rz_seg HKS HK1.
  pose proof (str_read m1 e TB ltac:(lia)) as RD.
  step. step. step. rewrite (yzext32_idiom e) by lia. step. clear RD.
  step. if_cases KC; zify_cond KC; revert KC; rewrite (Z_to_bv_small 8 (znth str e)) by (unfold bv_modulus; lia); rewrite ?unsigned_lit by lia; intros KC.
  - (* [comment removed for export] *)
    assert (NB : znth str e <> c_bslash) by (unfold c_bslash; lia).
    assert (SB1 : sbody_ix str (e + 1) n).
    { inversion SBX; subst; [lia| assumption| congruence| congruence]. }
    step. rewrite (unsigned_lit e) by lia. rewrite yswrap32_small by lia.
    step. if_cases KB; zify_cond KB.
    + apply evt_done.
      eapply (HEAD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 mo1 s1' errv1 b mb LK beg (e + 1) j0 j88);
        [ lk0 | exact HK1 | exact YS1 | exact FR | exact STK | exact MI | exact AX | exact ERR | exact PRES | exact YAF | exact TB
        | exact BR | exact BI | exact MBS | exact UB | lia | revert KB; rewrite ?unsigned_lit by lia; intros KB; lia | exact SB1 | lia | ].
      intros r Hr. apply HL. apply dlf_plain; [lia| exact NB| exact Hr].
    + step. apply evt_done.
      eapply (decode_exit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 mo1 s1' errv1 b mb LK beg (e + 1) (dblob j0 j88));
        [ lk0 | exact HK1 | exact YS1 | exact (dframe_blob _ j0 j88 FR) | exact STK | exact MI | exact AX | exact ERR | exact PRES | exact YAF | exact TB
        | exact BR | exact BI | exact MBS | lia | lia | revert KB; rewrite ?unsigned_lit by lia; intros KB; lia | ].
      apply exit_leaf. apply HL. apply dlf_plain; [lia| exact NB|]. destruct f' as [|f'']; [lia|]. apply dlf_exit.
      revert KB; rewrite ?unsigned_lit by lia; intros KB; lia.
  - (* [comment removed for export] *)
    assert (CB : znth str e = c_bslash) by (unfold c_bslash; lia).
    assert (E1 : e + 1 < n) by (inversion SBX; subst; [lia| congruence| lia| lia]).
    step. step. step. rewrite (yzext32_idiom beg) by lia. step. rewrite (unsigned_lit e), (unsigned_lit beg) by lia. rewrite yswrap32_small by lia.
    step. step.
    apply evt_done. clear MU WM.
    pose proof (zslice_length str beg (e - beg) ltac:(lia) ltac:(lia) ltac:(lia)) as ZL.
    eapply (YAP (LK ++ REST) mb b AF (S + beg) (zslice str beg (e - beg)) lo B errv1 K);
      [ exact K0 | apply RYST_split; split; [exact HK1| exact YS1] | exact BR | exact BI | exact YAF
      | exists hb; split; [apply in_or_app; right; exact HBI| lia]
      | apply bytes_at_zslice; [exact TB| lia]
      | apply Forall_zslice; exact SF
      | lia | rewrite ZL; lia | rewrite ZL; lia
      | rewrite ZL; destruct TR as [(bt & HBT & T1 & T2)|N0]; [left; exists bt; split; [apply in_or_app; right; exact HBT| lia]| right; right; right; lia]
      | lkr; exact YR
      | split; [exact AX|]; split; [rewrite ESP; lia|]; split; [rewrite ESP; exact STK|]; split; [exact CEIL|];
        split; [rewrite ESP; unfold RY_BUF_APPEND_STACK, RY_WRAP_STACK; lia|]; split; [rewrite (ry_errno_lit tp TP); exact ERR|]; split; [exact MI| exact TP]
      | reflexivity | reflexivity | rewrite ZL; reflexivity | ].
    cbv beta. intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 mo2 s2' b1 mb1 LK1 POST.
    destruct POST as ((MI2 & STK2 & (errv2 & ERR2) & AX2 & HP2) & YAF2 & HLB1 & BR2 & MBS1 & LKE2 & RY2). apply lk_hide in LKE2.
    replace (ret_pc (Z_to_bv 64 92600)) with (Z_to_bv 64 92600) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite ESP in STK2, HP2. rewrite (ry_errno_lit tp TP) in ERR2. unfold RERRNO in ERR2.
    pose proof (str_pres _ _ _ _ HP2 ltac:(intros b0 Hb0; apply in_or_app; right; exact Hb0) TB) as TB2.
    apply ry_pres_nil in HP2. apply RYST_split in RY2. destruct RY2 as [HK2 YS2].
    pose proof (ypres_frame _ _ _ _ _ _ HP2 FR ltac:(lia)) as FR2. clear FR.
    assert (PRES2 : ry_pres REST (bv_unsigned sp) [] m m2).
    { eapply ry_pres_trans; [exact PRES|]. apply ry_pres_of_rheap_pres. eapply rheap_pres_weaken; [exact HP2| lia| intros b0 Hb0; apply in_or_app; right; exact Hb0]. }
    pose proof (ypost_yleaf _ _ _ (ybuf_append_post2 b _ BI ltac:(rewrite ZL; lia)) HLB1) as BF. cbv beta in BF. destruct BF as (BI1 & OK1 & NOK1).
    assert (UB1 : yb_used b1 <= e).
    { destruct (yb_state b1); [destruct (OK1 eq_refl) as (_ & -> & _); rewrite ZL; lia| destruct (NOK1 ltac:(discriminate)) as [-> _]; lia| destruct (NOK1 ltac:(discriminate)) as [-> _]; lia]. }
    assert (MBS1' : mb_same mbd mb1) by (destruct MBS as [M1 M2]; destruct MBS1 as [M3 M4]; split; congruence).
    destruct MBS1 as [MID1 MAD1]. rewrite <- MAD1.
    clear HP2 MI STK ERR AX HK1 YS1 PRES TB BR YAF OK1 NOK1.
    pose proof (str_byte (e + 1) ltac:(lia)) as C1.
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
    rz_seg HKS HK2.
    step.
    pose proof (str_read m2 (e + 1) TB2 ltac:(lia)) as RD.
    step. step. step. rewrite (yzext32_idiom (e + 1)) by lia. step. clear RD.
    unfold zxb. rewrite (Z_to_bv_small 8 (znth str (e + 1))) by (unfold bv_modulus; lia).
    (* [comment removed for export] *)
    inversion SBX as [| i j Hlt Hnb Hrest| i j Hlt Hb Hvec Hrest| i j Hlt Hb Hu Hhex Hrest]; subst; [lia| congruence| |].
    + (* [comment removed for export] *)
      pose proof (vec_simple_escape _ Hvec) as HSE.
      destruct (simple_escape (znth str (e + 1))) as [u|] eqn:HU; [| congruence]. clear HSE.
      set (c1 := znth str (e + 1)) in *. assert (EC1 : c1 = znth str (e + 1)) by reflexivity. clearbody c1.
      assert (LIT : forall (U : Z) (slk : list Z) (a1x : word),
        bytes_at rsegs m2 U (zbytes ([u] ++ 0 :: slk)) -> Forall (fun c => 0 <= c < 256) ([u] ++ 0 :: slk) -> u <> 0 ->
        (- (U + 1 + 1)) mod 8 <= zlength slk -> 65536 <= U -> U + 1 <= 77824 ->
        realizes_cfg acfg rsegs (mkCfg (MS (mkR (Z_to_bv 64 92600) (Z_to_bv 64 (bv_unsigned sp + -208)) gp tp t0' t1' t2' (Z_to_bv 64 (mb_addr mb1)) (Z_to_bv 64 S)
              (Z_to_bv 64 c1) a1x a2' a3' a4' a5' a6' a7' (Z_to_bv 64 n) (Z_to_bv 64 U) (Z_to_bv 64 113) (Z_to_bv 64 34) (Z_to_bv 64 e) (Z_to_bv 64 64512) (Z_to_bv 64 (e + 1))
              (Z_to_bv 64 92) (Z_to_bv 64 101) (Z_to_bv 64 91) t3' t4' t5' t6') F (Z_to_bv 64 0x16c0c) fc None m2 (seg_rom rsegs)) mo2) K).
      { intros U slk a1x UBY UFA UNZ' USL ULO UHI.
        eapply (decode_lit f' HEAD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 mo2 s2' errv2 b1 mb1 (LK1 ++ LK) (e + 1) U [u] slk j0 j88);
          [ lk0 | rewrite <- app_assoc; exact HK2 | exact YS2 | exact FR2 | exact STK2 | exact MI2 | exact AX2 | exact ERR2 | exact PRES2 | exact YAF2 | exact TB2
          | exact BR2 | exact BI1 | exact MBS1' | exact UBY | exact UFA | intros [X|[]]; apply UNZ'; exact X | clear; cbn; lia | exact USL | lia
          | left; unfold zlength; cbn [length]; lia
          | unfold zlength; cbn [length]; lia | lia | lia | replace (e + 1 + 1) with (e + 2) by lia; exact Hrest | lia | ].
        intros r Hr. apply HL. eapply (dlf_esc f' b str n beg e u b1 r); [lia| exact CB| rewrite <- EC1; exact HU| exact HLB1| exact Hr]. }
      Ltac use_lit LIT U slk MI2 :=
        apply (LIT U slk); [ apply lit_bytes; [exact MI2| vm_compute; reflexivity| zle| zle]
                           | forall_bytes | discriminate | zle | zle | zle ].
      unfold simple_escape, c_r, c_n, c_bslash, c_slash, c_quote, c_f, c_b, c_t in HU.
      revert HU. destruct (Z.eqb_spec c1 114) as [EQ1|NE1]; intros HU.
      { assert (u = 13) as -> by congruence. subst c1.
        step. if_cases K2; zify_cond K2. 1:{ kill K2. } step. if_cases K3; zify_cond K3. 1:{ kill K3. }
        step. step. if_cases K4; zify_cond K4. 2:{ kill K4. } step. step. apply evt_done.
        use_lit LIT 66269 [47] MI2. }
      revert HU. destruct (Z.eqb_spec c1 110) as [EQ2|NE2]; intros HU.
      { assert (u = 10) as -> by congruence. subst c1.
        step. if_cases K2; zify_cond K2. 1:{ kill K2. } step. if_cases K3; zify_cond K3. 2:{ kill K3. }
        step. step. if_cases K4; zify_cond K4. 1:{ kill K4. } step. step. if_cases K5; zify_cond K5. 1:{ kill K5. }
        step. step. apply evt_done.
        use_lit LIT 67197 [121] MI2. }
      revert HU. destruct (Z.eqb_spec c1 92) as [EQ3|NE3]; intros HU.
      { assert (u = 92) as -> by congruence. subst c1.
        step. if_cases K2; zify_cond K2. 2:{ kill K2. } step. if_cases K3; zify_cond K3. 2:{ kill K3. }
        step. if_cases K4; zify_cond K4. 2:{ kill K4. } step. step. apply evt_done.
        use_lit LIT 66539 [0; 46; 0] MI2. }
      revert HU. destruct (Z.eqb_spec c1 47) as [EQ4|NE4]; intros HU.
      { assert (u = 47) as -> by congruence. subst c1.
        step. if_cases K2; zify_cond K2. 2:{ kill K2. } step. if_cases K3; zify_cond K3. 1:{ kill K3. }
        step. if_cases K4; zify_cond K4. 1:{ kill K4. } step. step. if_cases K5; zify_cond K5. 1:{ kill K5. }
        step. step. apply evt_done.
        use_lit LIT 66422 [99] MI2. }
      revert HU. destruct (Z.eqb_spec c1 34) as [EQ5|NE5]; intros HU.
      { assert (u = 34) as -> by congruence. subst c1.
        step. if_cases K2; zify_cond K2. 2:{ kill K2. } step. if_cases K3; zify_cond K3. 1:{ kill K3. }
        step. if_cases K4; zify_cond K4. 2:{ kill K4. } step. step. apply evt_done.
        use_lit LIT 67239 [42; 111; 117; 116; 76; 101; 110] MI2. }
      revert HU. destruct (Z.eqb_spec c1 102) as [EQ6|NE6]; intros HU.
      { assert (u = 12) as -> by congruence. subst c1.
        step. if_cases K2; zify_cond K2. 1:{ kill K2. } step. if_cases K3; zify_cond K3. 2:{ kill K3. }
        step. step. if_cases K4; zify_cond K4. 2:{ kill K4. } step. step. apply evt_done.
        use_lit LIT 67844 [111; 98; 115; 45; 62; 115; 105] MI2. }
      revert HU. destruct (Z.eqb_spec c1 98) as [EQ7|NE7]; intros HU.
      { assert (u = 8) as -> by congruence. subst c1.
        step. if_cases K2; zify_cond K2. 2:{ kill K2. } step. if_cases K3; zify_cond K3. 2:{ kill K3. }
        step. if_cases K4; zify_cond K4. 1:{ kill K4. } step. step. if_cases K5; zify_cond K5. 1:{ kill K5. }
        step. step. apply evt_done.
        use_lit LIT 67137 [47; 115; 114; 99; 47] MI2. }
      revert HU. destruct (Z.eqb_spec c1 116) as [EQ8|NE8]; intros HU; [| discriminate].
      { assert (u = 9) as -> by congruence. subst c1.
        step. if_cases K2; zify_cond K2. 1:{ kill K2. } step. if_cases K3; zify_cond K3. 1:{ kill K3. }
        step. step. if_cases K4; zify_cond K4. 1:{ kill K4. } step. step. if_cases K5; zify_cond K5. 2:{ kill K5. }
        step. step. apply evt_done.
        use_lit LIT 66968 [47; 115; 114; 99; 47; 121] MI2. }
    + (* [comment removed for export] *)
      rewrite Hu. unfold c_u.
      step. if_cases K2; zify_cond K2. 1:{ kill K2. } step. if_cases K3; zify_cond K3. 1:{ kill K3. }
      step. step. if_cases K4; zify_cond K4. 1:{ kill K4. } step. step. if_cases K5; zify_cond K5. 1:{ kill K5. }
      step. step. if_cases K6; zify_cond K6. 1:{ kill K6. }
      apply evt_done.
      eapply (decode_uesc f' HEAD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 mo2 s2' errv2 b b1 mb1 (LK1 ++ LK) beg e j0 j88);
        [ lk0 | rewrite <- app_assoc; exact HK2 | exact YS2 | exact FR2 | exact STK2 | exact MI2 | exact AX2 | exact ERR2 | exact PRES2 | exact YAF2 | exact TB2
        | exact BR2 | exact BI1 | exact MBS1' | exact UB1 | exact HBE | exact Hlt | exact CB | exact Hu | exact Hhex | exact Hrest | exact HF | exact HLB1 | exact HL ].
Qed.
End Fn.
End S.
End RC__2.
