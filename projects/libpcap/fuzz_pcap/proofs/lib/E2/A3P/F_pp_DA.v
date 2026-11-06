(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes Image ZBridge ITree Nodes Decode SysStep RegsEquiv Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim PcapPrelim PcapTypes PcapPure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF StrwF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA LibcKit Pcap_iface_ppA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require PP_kit2A F_pp_ctxA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_pp_BA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PP_kit2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pp_ctxA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pp_BA__A3P.F_pp_LA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pp_BA__A3P.F_pp_FA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
#[local] Ltac2 Set StepFast.sf_proj_inert := Ltac2.Init.true.
(* [comment removed for export] *)
Local Ltac acc_hint ::=
  lazymatch goal with
  | |- acc_in ?RNG (?a, _) =>
      let E := addr_expr a in let X := leftmost E in
      lazymatch X with
      | bv_unsigned _ => match goal with H : rng RNG ?lo ?len |- _ => first [ mentions len X | mentions lo X ]; solve_acc_with H end
      end
  end.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac bd_F := try lstep; bfalse.
Local Ltac bd_T := try lstep; btrue.
Local Ltac gsplit_FF x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb]; epilog | bd_F; cbn [orb andb negb]].
Local Ltac gsplit_FT x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb]; epilog | bd_T; cbn [orb andb negb]].
Local Ltac gsplit_TF x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; epilog | bd_F; cbn [orb andb negb]].
Local Ltac gsplit_TT x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; epilog | bd_T; cbn [orb andb negb]].
Local Ltac esplit_FF x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb] | bd_F; cbn [orb andb negb]].
Local Ltac esplit_FT x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb] | bd_T; cbn [orb andb negb]].
Local Ltac esplit_TF x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb] | bd_F; cbn [orb andb negb]].
Local Ltac esplit_TT x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb] | bd_T; cbn [orb andb negb]].
(* [comment removed for export] *)
Local Ltac zrange_gz_g :=
  lazymatch goal with
  | |- inr64 (Z.shiftl (Z.land (bv_unsigned (sx32 (Z_to_bv _ (get_le32 _ _)))) (65280)%Z) (8)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (bv_unsigned (sx32 (Z_to_bv _ (get_le32 _ _)))) (24)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (get_le32 _ _) (56)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (bv_swrap _ (Z.add (Z.add (64)%Z (Z.mul (16)%Z _)) (20)%Z)) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (Z.land (get_le32 _ _) (65280)%Z) (40)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (get_le32 _ _) (8)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (get_le32 _ _) (32)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (bv_swrap _ (Z.shiftr (bv_wrap _ (get_le32 _ _)) (24)%Z)) => fail   (* [comment removed for export] *)
  | |- _ => zrange
  end.
Local Ltac zrange_gz_i :=
  lazymatch goal with
  | |- _ => zrange
  end.
Local Ltac zsimp ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z;
  cbv delta [zxb];
  zb_fold_lits;
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) by zrange_gz_g
            | zs_wrap e ]            (* [comment removed for export] *)
  | |- _ => progress zs_idioms
  end; zb_fold_lits.
Local Ltac zsimp_in H ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z in H;
  cbv delta [zxb] in H;
  zb_fold_lits_in H;
  repeat match type of H with
  | context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) in H by zrange_gz_i
            | zs_wrap_in e H ]
  | _ => progress (zs_idioms_in H)
  end; zb_fold_lits_in H.
(* [comment removed for export] *)
Local Ltac run_stop :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    lazymatch pc with
    | 562784%Z => fail
    | 562860%Z => fail
    | 563068%Z => fail
    | 563188%Z => fail
    | 563284%Z => fail
    | 563380%Z => fail
    | 563480%Z => fail
    | 563616%Z => fail
    | 563712%Z => fail
    | 563808%Z => fail
    | 563900%Z => fail
    | 563952%Z => fail
    | 564016%Z => fail
    | 564096%Z => fail
    | 564172%Z => fail
    | 565936%Z => fail
    | 566036%Z => fail
    | _ => idtac
    end
  | |- _ => idtac
  end.
Local Ltac run ::= repeat (run_stop; lstep); try rewrite (sx32_small (c_caplen _)) by lia.
Lemma swap_usb_isodescs_S : forall f nd cap i desc off d,
  swap_usb_isodescs (S f) nd cap i desc off d =
  if i <? nd then
    if cap <? off + 4 then d
    else if cap <? off + 4 + 4 then swap_field 4 desc d
    else if cap <? off + 4 + 4 + 4 then swap_field 4 (desc + 4) (swap_field 4 desc d)
    else swap_usb_isodescs f nd cap (i + 1) (desc + 16) (off + 4 + 4 + 4 + 4)
           (swap_field 4 (desc + 8) (swap_field 4 (desc + 4) (swap_field 4 desc d)))
  else d.
Proof. reflexivity. Qed.
Lemma swap_usb_isodescs_exit : forall f nd cap i desc off d,
  ((i <? nd) = false \/ (cap <? off + 4) = true) -> swap_usb_isodescs f nd cap i desc off d = d.
Proof. intros [|f] nd cap i desc off d H; [reflexivity|]. rewrite swap_usb_isodescs_S. destruct H as [-> | ->]; [reflexivity|]. destruct (i <? nd); reflexivity. Qed.

Ltac close_inv := unfold ppinv; repeat match goal with |- _ /\ _ => split end; first [hyp_by_addr | assumption | reflexivity].
Ltac shreq := f_equal; rewrite !Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia.
Ltac wordeq ::= fastfirst (first [ noevar_assumption | reflexivity | (f_equal; lia) | (f_equal; rewrite ?swrap32_small by lia; lia) | (do 2 f_equal; lia)
                     | apply sx32_as_swrap | (symmetry; apply sx32_as_swrap) | shreq ]).
Ltac to_fixup WF' := eapply fixup_spec'; first [exact WF' | close_inv | reflexivity].

(* [comment removed for export] *)
Local Ltac ck_live OK pc := lazymatch constr:((OK, pc)) with (562632%Z, 562632%Z) => idtac | (562632%Z, 566312%Z) => idtac | (562652%Z, 562652%Z) => idtac | (562652%Z, 566332%Z) => idtac | (562668%Z, 562668%Z) => idtac | (562668%Z, 566352%Z) => idtac | (562676%Z, 562676%Z) => idtac | (562676%Z, 566372%Z) => idtac | (562832%Z, 562832%Z) => idtac | (562832%Z, 566608%Z) => idtac | (562844%Z, 562844%Z) => idtac | (562844%Z, 566628%Z) => idtac | (562892%Z, 562888%Z) => idtac | (562892%Z, 562892%Z) => idtac | (562892%Z, 566912%Z) => idtac | (562916%Z, 562912%Z) => idtac | (562916%Z, 562916%Z) => idtac | (562916%Z, 566936%Z) => idtac | (562936%Z, 562932%Z) => idtac | (562936%Z, 562936%Z) => idtac | (562936%Z, 566960%Z) => idtac | (562960%Z, 562956%Z) => idtac | (562960%Z, 562960%Z) => idtac | (562960%Z, 566984%Z) => idtac | (563124%Z, 563120%Z) => idtac | (563124%Z, 563124%Z) => idtac | (563124%Z, 567128%Z) => idtac | (563140%Z, 563136%Z) => idtac | (563140%Z, 563140%Z) => idtac | (563140%Z, 567152%Z) => idtac | (563220%Z, 563216%Z) => idtac | (563220%Z, 563220%Z) => idtac | (563220%Z, 567332%Z) => idtac | (563236%Z, 563232%Z) => idtac | (563236%Z, 563236%Z) => idtac | (563236%Z, 567356%Z) => idtac | (563316%Z, 563312%Z) => idtac | (563316%Z, 563316%Z) => idtac | (563316%Z, 567544%Z) => idtac | (563332%Z, 563328%Z) => idtac | (563332%Z, 563332%Z) => idtac | (563332%Z, 567568%Z) => idtac | (563412%Z, 563408%Z) => idtac | (563412%Z, 563412%Z) => idtac | (563412%Z, 567712%Z) => idtac | (563428%Z, 563424%Z) => idtac | (563428%Z, 563428%Z) => idtac | (563428%Z, 567736%Z) => idtac | (563500%Z, 563496%Z) => idtac | (563500%Z, 563500%Z) => idtac | (563500%Z, 567756%Z) => idtac | (563552%Z, 563548%Z) => idtac | (563552%Z, 563552%Z) => idtac | (563552%Z, 567888%Z) => idtac | (563568%Z, 563564%Z) => idtac | (563568%Z, 563568%Z) => idtac | (563568%Z, 567912%Z) => idtac | (563648%Z, 563644%Z) => idtac | (563648%Z, 563648%Z) => idtac | (563648%Z, 568016%Z) => idtac | (563664%Z, 563660%Z) => idtac | (563664%Z, 563664%Z) => idtac | (563664%Z, 568040%Z) => idtac | (563744%Z, 563740%Z) => idtac | (563744%Z, 563744%Z) => idtac | (563744%Z, 568104%Z) => idtac | (563760%Z, 563756%Z) => idtac | (563760%Z, 563760%Z) => idtac | (563760%Z, 568128%Z) => idtac | (563840%Z, 563836%Z) => idtac | (563840%Z, 563840%Z) => idtac | (563840%Z, 568152%Z) => idtac | (563856%Z, 563852%Z) => idtac | (563856%Z, 563856%Z) => idtac | (563856%Z, 568176%Z) => idtac | (563964%Z, 563964%Z) => idtac | (563964%Z, 564208%Z) => idtac | (563976%Z, 563976%Z) => idtac | (563976%Z, 564224%Z) => idtac | (564044%Z, 564044%Z) => idtac | (564044%Z, 564240%Z) => idtac | (564056%Z, 564056%Z) => idtac | (564056%Z, 564256%Z) => idtac | (564124%Z, 564124%Z) => idtac | (564124%Z, 564272%Z) => idtac | (564136%Z, 564136%Z) => idtac | (564136%Z, 564288%Z) => idtac | (565880%Z, 565880%Z) => idtac | (565880%Z, 567944%Z) => idtac | (565892%Z, 565892%Z) => idtac | (565892%Z, 567964%Z) => idtac | (565980%Z, 565980%Z) => idtac | (565980%Z, 568052%Z) => idtac | (565992%Z, 565992%Z) => idtac | (565992%Z, 568072%Z) => idtac end.
Local Ltac ck_arm OK n ::=
  lazymatch n with
  | O => fail "ck_join: step budget exhausted before reaching the join point" OK
  | S ?n' =>
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 OK) _ _ _ _) =>
        apply evtF_done; cbn [ck_post]; repeat eexists; simp_regs;
        first [ reflexivity | fail 1 "ck_join: a register outside the clobber list changed before" OK ]
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep; rewrite ?sxb_sval; ck_arm OK n'
    | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
        let K := fresh "Kck" in
        if_cases K; ck_zify K;
        lazymatch goal with
        | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => tryif ck_live OK pc then first [ ck_arm OK n' | exfalso; ck_lia ] else first [ exfalso; ck_lia | ck_arm OK n' ]
        | _ => first [ exfalso; ck_lia | ck_arm OK n' ]
        end
    end
  end.
Section CANSEC1. Context {rc : runConstT}.

Definition isoloop_spec__stmt : Prop := forall c, ppwf c -> forall (f : nat) (i : Z),
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 : word) m d (nd : Z),
  ppinv c m d (c_len0 c) ->
  (16 * Z.of_nat f >= c_caplen c - (64 + 16 * i) + 12)%Z ->
  (0 <= i < nd)%Z -> (64 + 16 * i + 4 <= c_caplen c)%Z -> (0 <= nd < 2^32)%Z ->
  a0 = Z_to_bv 64 220 -> a2 = Z_to_bv 64 (c_HA c) -> a3 = Z_to_bv 64 (c_DA c) -> a6 = SBW -> a5 = Z_to_bv 64 (c_caplen c) ->
  a1 = Z_to_bv 64 (c_DA c + (64 + 16 * i)) -> t3 = Z_to_bv 64 (c_DA c + (64 + 16 * i)) ->
  t1 = Z_to_bv 64 (Z.shiftr (c_DA c + (64 + 16 * i)) 3 + 2147450880) ->
  t0 = Z_to_bv 64 (i + 1) -> a4 = Z_to_bv 64 (bv_swrap 32 (64 + 16 * i + 20)) ->
  a7 = sx32 (Z_to_bv 64 nd) -> t2 = Z_to_bv 64 65280 ->
  evtF asegs (c_RNG c)
      (let D := swap_usb_isodescs f nd (c_caplen c) i (64 + 16 * i) (64 + 16 * i) d in
       ppost c (h_len (fixup_usb_mmapped_len (mkHdr 0 0 (c_caplen c) (c_len0 c)) D)) D)
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x89af0) (c_fc c) None m (seg_rom asegs)).
Section Sz3.
Variables c : ltac2:(SecDiet.SzSec.tyM 'isoloop_spec__stmt "vhk" @c).
#[using="Type"] Lemma isoloop_spec__body : ltac2:(SecDiet.SzSec.bodyP 'isoloop_spec__stmt "vhk").
Proof.
  intros f WF.
 induction f as [|f IH]; intros i; intros until nd; intros I FU IR CI ND -> -> -> -> -> -> -> -> -> -> -> ->.
  { exfalso. lia. }
  pose proof WF as WF'. pp_init WF I. cbv zeta.
  rewrite swap_usb_isodescs_S.
  replace (i <? nd) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (c_caplen c <? 64 + 16 * i + 4) with false by (symmetry; apply Z.ltb_ge; lia). simpl_if.
  ckp_at UNPD (c_DA c + (64 + 16 * i))%Z 4%Z. do 2 zstep. ck_cut 0x89afc%Z [14%Z].
  zstep. rd4 (64 + 16 * i)%Z. ck_cut 0x89b08%Z [31%Z]. ckp_clear.
  run. st4 (64 + 16 * i)%Z.
  run. rf_norm.
  destruct (Z.ltb_spec (c_caplen c) (64 + 16 * i + 8)) as [C1|C1].
  { bd_T. simpl_if. to_fixup WF'. }
  bd_F. simpl_if.
  zstep. ckp_at UNPD (c_DA c + (64 + 16 * i) + 4)%Z 4%Z. do 3 zstep. ck_cut 0x89b4c%Z [8%Z].
  zstep. rd4 (64 + 16 * i + 4)%Z. ck_cut 0x89b58%Z [8%Z]. ckp_clear.
  run. st4 (64 + 16 * i + 4)%Z.
  run. rf_norm.
  destruct (Z.ltb_spec (c_caplen c) (64 + 16 * i + 12)) as [C2|C2].
  { bd_T. simpl_if. to_fixup WF'. }
  bd_F. simpl_if.
  zstep. ckp_at UNPD (c_DA c + (64 + 16 * i) + 8)%Z 4%Z. do 3 zstep. ck_cut 0x89b9c%Z [8%Z].
  zstep. rd4 (64 + 16 * i + 8)%Z. ck_cut 0x89ba8%Z [8%Z]. ckp_clear.
  run. st4 (64 + 16 * i + 8)%Z.
  run.
  destruct (Z.ltb_spec (i + 1) nd) as [IN|IN]; cycle 1.
  { bd_T. rewrite swap_usb_isodescs_exit by (left; apply Z.ltb_ge; lia). to_fixup WF'. }
  bd_F. run. rf_norm.
  destruct (Z.ltb_spec (c_caplen c) (64 + 16 * i + 20)) as [C5|C5].
  { bd_F. lstep. rewrite swap_usb_isodescs_exit by (right; apply Z.ltb_lt; lia). to_fixup WF'. }
  bd_T.
  replace (64 + 16 * i + 16)%Z with (64 + 16 * (i + 1))%Z by lia.
  replace (64 + 16 * i + 4 + 4 + 4 + 4)%Z with (64 + 16 * (i + 1))%Z by lia.
  eapply (IH (i + 1)%Z); fastfirst (first [ noevar_assumption | close_inv | wordeq | lia]).
Qed.
End Sz3.
#[using="Type"] Lemma isoloop_spec : ltac:(let t := eval cbv delta [isoloop_spec__stmt] in isoloop_spec__stmt in exact t).
Proof. intros c WF f. ltac2:(SecDiet.SzSec.closeP 'isoloop_spec__body "vhk"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition usbmm_k (caplen : Z) (d : list Z) : list Z :=
  (if caplen <? 52 then d else
   let d := swap_field 4 48 d in
   if caplen <? 56 then d else
   let d := swap_field 4 52 d in
   if caplen <? 60 then d else
   let d := swap_field 4 56 d in
   if caplen <? 64 then d else
   let d := swap_field 4 60 d in
   if get_u8 d 9 =? 0 then swap_usb_isodescs (Z.to_nat (caplen / 16 + 2)) (get_le32 d 60) caplen 0 64 64 d else d)%Z.

(* [comment removed for export] *)
Ltac gsplitA WF' x k :=
  let C := fresh "Hc" in
  destruct (Z.ltb_spec x k) as [C|C];
  [ bdecide; cbn [orb andb negb]; simpl_if; eapply fixup_spec; fastfirst (first [exact WF' | close_inv | reflexivity])
  | bdecide; cbn [orb andb negb] ].
Local Ltac gsplitA__c1 WF' x k :=
  let C := fresh "Hc" in
  destruct (Z.ltb_spec x k) as [C|C];
  [ bd_T; cbn [orb andb negb]; simpl_if; eapply fixup_spec; fastfirst (first [exact WF' | close_inv | reflexivity])
  | bd_F; cbn [orb andb negb] ].
Local Ltac gsplitA__c2 WF' x k :=
  let C := fresh "Hc" in
  destruct (Z.ltb_spec x k) as [C|C];
  [ bd_T; cbn [orb andb negb]; simpl_if; eapply fixup_spec; fastfirst (first [exact WF' | close_inv | reflexivity])
  | bd_F; cbn [orb andb negb] ].
Local Ltac gsplitA__c3 WF' x k :=
  let C := fresh "Hc" in
  destruct (Z.ltb_spec x k) as [C|C];
  [ bd_T; cbn [orb andb negb]; simpl_if; eapply fixup_spec; fastfirst (first [exact WF' | close_inv | reflexivity])
  | bd_F; cbn [orb andb negb] ].
Local Ltac gsplitA__c4 WF' x k :=
  let C := fresh "Hc" in
  destruct (Z.ltb_spec x k) as [C|C];
  [ bd_T; cbn [orb andb negb]; simpl_if; eapply fixup_spec; fastfirst (first [exact WF' | close_inv | reflexivity])
  | bd_F; cbn [orb andb negb] ].
Local Ltac gsplitA__c5 WF' x k :=
  let C := fresh "Hc" in
  destruct (Z.ltb_spec x k) as [C|C];
  [ bd_T; cbn [orb andb negb]; simpl_if; eapply fixup_spec; fastfirst (first [exact WF' | close_inv | reflexivity])
  | bd_F; cbn [orb andb negb] ].
Local Ltac gsplitA__c6 WF' x k :=
  let C := fresh "Hc" in
  destruct (Z.ltb_spec x k) as [C|C];
  [ bd_T; cbn [orb andb negb]; simpl_if; eapply fixup_spec; fastfirst (first [exact WF' | close_inv | reflexivity])
  | bd_F; cbn [orb andb negb] ].
Local Ltac gsplitA__c7 WF' x k :=
  let C := fresh "Hc" in
  destruct (Z.ltb_spec x k) as [C|C];
  [ bd_T; cbn [orb andb negb]; simpl_if; eapply fixup_spec; fastfirst (first [exact WF' | close_inv | reflexivity])
  | bd_F; cbn [orb andb negb] ].
Local Ltac gsplitA__c8 WF' x k :=
  let C := fresh "Hc" in
  destruct (Z.ltb_spec x k) as [C|C];
  [ bd_T; cbn [orb andb negb]; simpl_if; eapply fixup_spec; fastfirst (first [exact WF' | close_inv | reflexivity])
  | bd_F; cbn [orb andb negb] ].
Local Ltac gsplitA__c9 WF' x k :=
  let C := fresh "Hc" in
  destruct (Z.ltb_spec x k) as [C|C];
  [ bd_T; cbn [orb andb negb]; simpl_if; eapply fixup_spec; fastfirst (first [exact WF' | close_inv | reflexivity])
  | bd_F; cbn [orb andb negb] ].
Local Ltac gsplitA__c10 WF' x k :=
  let C := fresh "Hc" in
  destruct (Z.ltb_spec x k) as [C|C];
  [ bd_T; cbn [orb andb negb]; simpl_if; eapply fixup_spec; fastfirst (first [exact WF' | close_inv | reflexivity])
  | bd_F; cbn [orb andb negb] ].
Local Ltac gsplitA__c11 WF' x k :=
  let C := fresh "Hc" in
  destruct (Z.ltb_spec x k) as [C|C];
  [ bd_T; cbn [orb andb negb]; simpl_if; eapply fixup_spec; fastfirst (first [exact WF' | close_inv | reflexivity])
  | bd_F; cbn [orb andb negb] ].
Local Ltac gsplitA__c12 WF' x k :=
  let C := fresh "Hc" in
  destruct (Z.ltb_spec x k) as [C|C];
  [ bd_T; cbn [orb andb negb]; simpl_if; eapply fixup_spec; fastfirst (first [exact WF' | close_inv | reflexivity])
  | bd_F; cbn [orb andb negb] ].
Local Ltac gsplitA__c13 WF' x k :=
  let C := fresh "Hc" in
  destruct (Z.ltb_spec x k) as [C|C];
  [ bd_T; cbn [orb andb negb]; simpl_if; eapply fixup_spec; fastfirst (first [exact WF' | close_inv | reflexivity])
  | bd_F; cbn [orb andb negb] ].

Definition usbmm_tail_spec__stmt : Prop := forall c, ppwf c ->
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 : word) m d,
  ppinv c m d (c_len0 c) ->
  a0 = Z_to_bv 64 220 -> a2 = Z_to_bv 64 (c_HA c) -> a3 = Z_to_bv 64 (c_DA c) -> a6 = SBW ->
  a1 = Z_to_bv 64 (c_HA c + 16) -> t0 = Z_to_bv 64 (get_u8 d 9) ->
  evtF asegs (c_RNG c)
      (let D := usbmm_k (c_caplen c) d in
       ppost c (h_len (fixup_usb_mmapped_len (mkHdr 0 0 (c_caplen c) (c_len0 c)) D)) D)
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x8993c) (c_fc c) None m (seg_rom asegs)).
Section Sz4.
Variables c : ltac2:(SecDiet.SzSec.tyM 'usbmm_tail_spec__stmt "v" @c).
#[using="Type"] Lemma usbmm_tail_spec__body : ltac2:(SecDiet.SzSec.bodyP 'usbmm_tail_spec__stmt "v").
Proof.
  intros WF; intros until d; intros I -> -> -> -> -> ->.
 pose proof WF as WF'. pp_init WF I. cbv zeta. unfold usbmm_k.
  pose proof (get_u8_range d 9 ZR) as U9.
  do 2 lstep. rewrite (sx32_small (c_caplen _)) by lia. gsplitA__c1 WF' (c_caplen c) 52%Z.
  zstep. ckp_at UNPD (c_DA c + 48)%Z 4%Z. do 3 zstep. ck_cut 0x89960%Z [6%Z]. zstep. rd4 48%Z. ck_cut 0x89970%Z [6%Z]. ckp_clear.
  run. st4 48%Z. gsplitA__c2 WF' (c_caplen c) 56%Z.
  zstep. ckp_at UNPD (c_DA c + 52)%Z 4%Z. do 3 zstep. ck_cut 0x899c0%Z [6%Z]. zstep. rd4 52%Z. ck_cut 0x899d0%Z [6%Z]. ckp_clear.
  run. st4 52%Z. gsplitA__c3 WF' (c_caplen c) 60%Z.
  zstep. ckp_at UNPD (c_DA c + 56)%Z 4%Z. do 3 zstep. ck_cut 0x89a20%Z [6%Z]. zstep. rd4 56%Z. ck_cut 0x89a30%Z [6%Z]. ckp_clear.
  run. st4 56%Z. gsplitA__c4 WF' (c_caplen c) 64%Z.
  zstep. ckp_at UNPD (c_DA c + 60)%Z 4%Z. do 3 zstep. ck_cut 0x89a80%Z [6%Z]. zstep. rd4 60%Z. ck_cut 0x89a90%Z [6%Z]. ckp_clear.
  run.
  name4 60%Z. st4 60%Z. fix_u8_all 9%Z.
  lazymatch goal with Hd : ?dn = swap_field 4 60 ?dold, EW : zslice 60 4 ?dold = [?y0; ?y1; ?y2; ?y3] |- _ =>
    let ND := fresh "ND" in
    assert (ND : get_le32 dn 60 = (y3 + 256 * y2 + 65536 * y1 + 16777216 * y0)%Z)
      by (rewrite Hd; unfold swap_field; rewrite EW; cbn [rev app]; apply get_le32_write_same; lia);
    rewrite ND;
    let EX := fresh "EX" in pose proof (get_le32_of_slice _ _ _ _ _ _ EW) as EX;
    match goal with |- context [Z_to_bv 64 ?E] =>
      lazymatch E with context [get_le32 dold 60] =>
        lazymatch E with Z.lor (Z.lor _ _) _ =>
          replace (Z_to_bv 64 E) with (sx32 (Z_to_bv 64 (y3 + 256 * y2 + 65536 * y1 + 16777216 * y0)%Z))
            by (rewrite <- (Z_to_bv_bv_unsigned (sx32 _)); f_equal;
                replace (y3 + 256 * y2 + 65536 * y1 + 16777216 * y0)%Z with (le_of_bytes [y3; y2; y1; y0]) by (cbn; lia);
                unfold get_le32; rewrite EW; repeat lanes_step; fastfirst (first [reflexivity | cbn [le_of_bytes]; lia]))
        end end end;
    let NDR := fresh "NDR" in
    assert (NDR : (0 <= y3 + 256 * y2 + 65536 * y1 + 16777216 * y0 < 2^32)%Z) by lia;
    set (nd := (y3 + 256 * y2 + 65536 * y1 + 16777216 * y0)%Z) in *
  end.
  destruct (Z.eqb_spec (get_u8 d 9) 0) as [TT|TT]; simpl_if; cycle 1.
  { bd_T. eapply fixup_spec; fastfirst (first [exact WF' | close_inv | reflexivity]). }
  bd_F. run.
  destruct (Z.ltb_spec (c_caplen c) 68) as [C68|C68].
  { bd_T. rewrite swap_usb_isodescs_exit by (right; apply Z.ltb_lt; lia).
    eapply fixup_spec; fastfirst (first [exact WF' | close_inv | reflexivity]). }
  bd_F.
  destruct (Z.eqb_spec nd 0) as [N0|N0].
  { bd_T. rewrite swap_usb_isodescs_exit by (left; apply Z.ltb_ge; lia).
    eapply fixup_spec; fastfirst (first [exact WF' | close_inv | reflexivity]). }
  rewrite EX. bd_F. run.
  eapply (isoloop_spec c WF' (Z.to_nat (c_caplen c / 16 + 2)) 0%Z); fastfirst (first [ noevar_assumption | close_inv | wordeq | lia]).
Qed.
End Sz4.
#[using="Type"] Lemma usbmm_tail_spec : ltac:(let t := eval cbv delta [usbmm_tail_spec__stmt] in usbmm_tail_spec__stmt in exact t).
Proof. intros c. ltac2:(SecDiet.SzSec.closeP 'usbmm_tail_spec__body "v"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac to_tail WF' :=
  lazymatch goal with ZB : bytes_at asegs _ _ (zbytes ?dd) |- _ =>
    eapply usbmm_tail_spec with (d := dd);
    fastfirst (first [ exact WF' | close_inv | reflexivity | (f_equal; symmetry; fix_u8_all 9%Z; reflexivity) ]) end.

Definition usbmm_spec__stmt : Prop := forall c, ppwf c ->
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 : word) m d,
  ppinv c m d (c_len0 c) ->
  a0 = Z_to_bv 64 220 -> a2 = Z_to_bv 64 (c_HA c) -> a3 = Z_to_bv 64 (c_DA c) -> a6 = SBW ->
  evtF asegs (c_RNG c)
      (let D := swap_linux_usb_header (mkHdr 0 0 (c_caplen c) (c_len0 c)) d true in
       ppost c (h_len (fixup_usb_mmapped_len (mkHdr 0 0 (c_caplen c) (c_len0 c)) D)) D)
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x89598) (c_fc c) None m (seg_rom asegs)).
Section Sz5.
Variables c : ltac2:(SecDiet.SzSec.tyM 'usbmm_spec__stmt "v" @c).
#[using="Type"] Lemma usbmm_spec__body : ltac2:(SecDiet.SzSec.bodyP 'usbmm_spec__stmt "v").
Proof.
  intros WF; intros until d; intros I -> -> -> ->.
 pose proof WF as WF'. pp_init WF I. cbv zeta.
  unfold swap_linux_usb_header. cbn [h_caplen h_len]. unfold URB_ISOCHRONOUS.
  zstep. ck0 UNPH; ck_go.
  do 2 lstep. rewrite (sx32_small (c_caplen _)) by lia. gsplitA__c5 WF' (c_caplen c) 8%Z.
  (* [comment removed for export] *)
  ckp_at UNPD (c_DA c) 1%Z. do 3 zstep. ck_cut 0x895c8%Z [5%Z]. ckp_clear.
  zstep. ckp_at UNPD (c_DA c + 7)%Z 1%Z. do 3 zstep. ck_cut 0x895dc%Z [7%Z]. ckp_clear.
  ckp_at UNPD (c_DA c) 1%Z. zstep. rd4 0%Z. rd4 4%Z. ck_cut 0x895ec%Z [28%Z]. ckp_clear.
  ckp_at UNPD (c_DA c + 7)%Z 1%Z. zstep. ck_cut 0x895f4%Z [7%Z]. ckp_clear.
  run. st8 0%Z.
  ck0_at UNPH (c_HA c + 16)%Z; ck_go.
  do 2 lstep. rewrite (sx32_small (c_caplen _)) by lia. gsplitA__c6 WF' (c_caplen c) 14%Z.
  (* [comment removed for export] *)
  zstep. ckp_at UNPD (c_DA c + 12)%Z 2%Z. do 3 zstep. ck_cut 0x89690%Z [7%Z]. zstep. rd2 12%Z. ck_cut 0x8969c%Z [7%Z]. ckp_clear.
  run. st2 12%Z. gsplitA__c7 WF' (c_caplen c) 24%Z.
  (* [comment removed for export] *)
  zstep. ckp_at UNPD (c_DA c + 16)%Z 1%Z. do 3 zstep. ck_cut 0x896cc%Z [6%Z]. ckp_clear.
  zstep. ckp_at UNPD (c_DA c + 23)%Z 1%Z. do 3 zstep. ck_cut 0x896e4%Z [7%Z]. ckp_clear.
  ckp_at UNPD (c_DA c + 16)%Z 1%Z. zstep. rd4 16%Z. rd4 20%Z. ck_cut 0x896f8%Z [7%Z]. ckp_clear.
  zstep. ckp_at UNPD (c_DA c + 23)%Z 1%Z. do 3 zstep. ck_cut 0x89710%Z [28%Z]. ckp_clear.
  run. st8 16%Z.
  ck0_at UNPH (c_HA c + 16)%Z; ck_go.
  do 2 lstep. rewrite (sx32_small (c_caplen _)) by lia. gsplitA__c8 WF' (c_caplen c) 28%Z.
  (* [comment removed for export] *)
  zstep. ckp_at UNPD (c_DA c + 24)%Z 4%Z. do 3 zstep. ck_cut 0x897b4%Z [7%Z]. zstep. rd4 24%Z. ck_cut 0x897c4%Z [7%Z]. ckp_clear.
  run. st4 24%Z. gsplitA__c9 WF' (c_caplen c) 32%Z.
  zstep. ckp_at UNPD (c_DA c + 28)%Z 4%Z. do 3 zstep. ck_cut 0x89814%Z [7%Z]. zstep. rd4 28%Z. ck_cut 0x89824%Z [7%Z]. ckp_clear.
  run. st4 28%Z. gsplitA__c10 WF' (c_caplen c) 36%Z.
  zstep. ckp_at UNPD (c_DA c + 32)%Z 4%Z. do 3 zstep. ck_cut 0x89874%Z [7%Z]. zstep. rd4 32%Z. ck_cut 0x89884%Z [7%Z]. ckp_clear.
  run. st4 32%Z. gsplitA__c11 WF' (c_caplen c) 40%Z.
  zstep. ckp_at UNPD (c_DA c + 36)%Z 4%Z. do 3 zstep. ck_cut 0x898d4%Z [7%Z]. zstep. rd4 36%Z. ck_cut 0x898e4%Z [7%Z]. ckp_clear.
  run.
  st4 36%Z.
  ckp_at UNPD (c_DA c + 9)%Z 1%Z. do 2 zstep. ck_cut 0x8992c%Z [6%Z]. ckp_clear.
  rd1 9%Z.
  lazymatch goal with |- context [get_u8 ?dd 9 =? 0] => esplit_TF (get_u8 dd 9) 0%Z end.
  - (* [comment removed for export] *)
    lstep. gsplitA__c12 WF' (c_caplen c) 44%Z.
    zstep. ckp_at UNPD (c_DA c + 40)%Z 4%Z. do 3 zstep. ck_cut 0x8a278%Z [7%Z]. zstep. rd4 40%Z. ck_cut 0x8a284%Z [7%Z]. ckp_clear.
    run. st4 40%Z.
    ck0_at UNPH (c_HA c + 16)%Z; ck_go.
    do 2 lstep. rewrite (sx32_small (c_caplen _)) by lia. gsplitA__c13 WF' (c_caplen c) 48%Z.
    zstep. ckp_at UNPD (c_DA c + 44)%Z 4%Z. do 3 zstep. ck_cut 0x8a2dc%Z [7%Z]. zstep. rd4 44%Z. ck_cut 0x8a2e8%Z [7%Z]. ckp_clear.
    run. st4 44%Z.
    ck0_at UNPH (c_HA c + 16)%Z; ck_go.
    to_tail WF'.
  - (* [comment removed for export] *)
    ck0_at UNPH (c_HA c + 16)%Z; ck_go. to_tail WF'.
Qed.
End Sz5.
#[using="Type"] Lemma usbmm_spec : ltac:(let t := eval cbv delta [usbmm_spec__stmt] in usbmm_spec__stmt in exact t).
Proof. intros c. ltac2:(SecDiet.SzSec.closeP 'usbmm_spec__body "v"). Qed.

End CANSEC1.
