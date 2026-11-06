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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA Pcap_iface_ppA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require PP_kit2A F_pp_ctxA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PP_kit2A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pp_ctxA.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
#[local] Ltac2 Set StepFast.sf_proj_inert := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac acc_hint ::=
  lazymatch goal with
  | |- acc_in ?RNG (?a, _) =>
      let E := addr_expr a in let X := leftmost E in
      lazymatch X with
      | bv_unsigned _ =>
          first [ match goal with H : rng RNG ?lo ?len |- _ => first [ mentions len X | mentions lo X ]; solve_acc_with H end
                | match goal with H : rng RNG (c_lo _) _ |- _ => solve_acc_with H end ]
      end
  end.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Ltac rf_norm := rewrite ?sx32_as_swrap, ?unsigned_RF, ?swrap32_add_mod64_l, ?swrap32_add_mod64_r, ?swrap32_sub_mod64_l, ?Z.add_0_r.
Ltac wordeq := fastfirst (first [ noevar_assumption | reflexivity | (f_equal; lia) | (f_equal; rewrite ?swrap32_small by lia; lia) | (do 2 f_equal; lia)
                     | apply sx32_as_swrap | (symmetry; apply sx32_as_swrap) ]).

(* [comment removed for export] *)
Local Ltac bd_F := try lstep; try untrap; bfalse.
Local Ltac bd_T := try lstep; try untrap; btrue.
Local Ltac gsplit_FF x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb]; epilog | bd_F; cbn [orb andb negb]].
Local Ltac gsplit_FT x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb]; epilog | bd_T; cbn [orb andb negb]].
Local Ltac gsplit_TF x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; epilog | bd_F; cbn [orb andb negb]].
Local Ltac gsplit_TT x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; epilog | bd_T; cbn [orb andb negb]].
Local Ltac esplit_FF x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb] | bd_F; cbn [orb andb negb]].
Local Ltac esplit_FT x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb] | bd_T; cbn [orb andb negb]].
Local Ltac esplit_TF x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb] | bd_F; cbn [orb andb negb]].
Local Ltac esplit_TT x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb] | bd_T; cbn [orb andb negb]].
(* [comment removed for export] *)
Local Ltac kt_data e := lazymatch e with context [get_le32 _ _] => idtac | context [get_le16 _ _] => idtac | context [get_u8 _ _] => idtac end.
Local Ltac kt_big e := lazymatch e with Z.lor _ _ => kt_data e | Z.land _ _ => kt_data e | Z.shiftl _ _ => kt_data e | Z.shiftr _ _ => kt_data e | Z.modulo _ _ => kt_data e end.
Local Ltac kill_towers := repeat (lazymatch goal with |- evtF _ _ _ (MS ?R _ _ _ _ _ _) =>
  match R with context [Z_to_bv _ ?e] => kt_big e; let v := fresh "kv" in generalize (Z_to_bv 64 e) as v; intro v end end).
Local Ltac alia ::= lia.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac ck_live OK pc := lazymatch constr:((OK, pc)) with (565836%Z, 565836%Z) => idtac | (565836%Z, 567668%Z) => idtac | (565856%Z, 565856%Z) => idtac | (565856%Z, 567688%Z) => idtac | (565872%Z, 565872%Z) => idtac | (565872%Z, 567708%Z) => idtac | (565880%Z, 565880%Z) => idtac | (565880%Z, 567728%Z) => idtac | (566036%Z, 566036%Z) => idtac | (566036%Z, 567764%Z) => idtac | (566048%Z, 566048%Z) => idtac | (566048%Z, 567784%Z) => idtac | (566092%Z, 566092%Z) => idtac | (566092%Z, 567804%Z) => idtac | (566112%Z, 566112%Z) => idtac | (566112%Z, 567824%Z) => idtac | (566128%Z, 566128%Z) => idtac | (566128%Z, 567844%Z) => idtac | (566148%Z, 566148%Z) => idtac | (566148%Z, 567864%Z) => idtac | (566304%Z, 566304%Z) => idtac | (566304%Z, 567900%Z) => idtac | (566316%Z, 566316%Z) => idtac | (566316%Z, 567920%Z) => idtac | (566392%Z, 566392%Z) => idtac | (566392%Z, 567940%Z) => idtac | (566404%Z, 566404%Z) => idtac | (566404%Z, 567960%Z) => idtac | (566480%Z, 566480%Z) => idtac | (566480%Z, 567980%Z) => idtac | (566492%Z, 566492%Z) => idtac | (566492%Z, 568000%Z) => idtac | (566568%Z, 566568%Z) => idtac | (566568%Z, 568020%Z) => idtac | (566580%Z, 566580%Z) => idtac | (566580%Z, 568040%Z) => idtac | (566648%Z, 566648%Z) => idtac | (566648%Z, 568060%Z) => idtac | (566700%Z, 566700%Z) => idtac | (566700%Z, 568092%Z) => idtac | (566712%Z, 566712%Z) => idtac | (566712%Z, 568108%Z) => idtac | (566788%Z, 566788%Z) => idtac | (566788%Z, 568180%Z) => idtac | (566800%Z, 566800%Z) => idtac | (566800%Z, 568196%Z) => idtac | (566876%Z, 566876%Z) => idtac | (566876%Z, 568252%Z) => idtac | (566888%Z, 566888%Z) => idtac | (566888%Z, 568268%Z) => idtac | (566964%Z, 566964%Z) => idtac | (566964%Z, 568284%Z) => idtac | (566976%Z, 566976%Z) => idtac | (566976%Z, 568300%Z) => idtac | (567096%Z, 567096%Z) => idtac | (567096%Z, 567344%Z) => idtac | (567108%Z, 567108%Z) => idtac | (567108%Z, 567360%Z) => idtac | (567176%Z, 567176%Z) => idtac | (567176%Z, 567376%Z) => idtac | (567188%Z, 567188%Z) => idtac | (567188%Z, 567392%Z) => idtac | (567256%Z, 567256%Z) => idtac | (567256%Z, 567408%Z) => idtac | (567268%Z, 567268%Z) => idtac | (567268%Z, 567424%Z) => idtac | (567472%Z, 567472%Z) => idtac | (567472%Z, 568124%Z) => idtac | (567484%Z, 567484%Z) => idtac | (567484%Z, 568144%Z) => idtac | (567572%Z, 567572%Z) => idtac | (567572%Z, 568212%Z) => idtac | (567584%Z, 567584%Z) => idtac | (567584%Z, 568232%Z) => idtac end.
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
(* [comment removed for export] *)
Local Ltac run_stop :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    lazymatch pc with
    | 565988%Z => fail
    | 566064%Z => fail
    | 566256%Z => fail
    | 566364%Z => fail
    | 566452%Z => fail
    | 566540%Z => fail
    | 566632%Z => fail
    | 566760%Z => fail
    | 566848%Z => fail
    | 566936%Z => fail
    | 567020%Z => fail
    | 567084%Z => fail
    | 567148%Z => fail
    | 567228%Z => fail
    | 567304%Z => fail
    | 567528%Z => fail
    | 567628%Z => fail
    | _ => idtac
    end
  | |- _ => idtac
  end.
Local Ltac run ::= repeat (run_stop; lstep); try rewrite (sx32_small (c_caplen _)) by lia.
Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition UW (c : ppctx) (spv : Z) : list (Z * Z) := [(spv - 16, spv); (c_DA c, c_DA c + c_caplen c)]%Z.

(* [comment removed for export] *)
Definition uhinv (c : ppctx) (spv : Z) (m0 m : mem) (d : list Z) (hlen : Z) (j0 : list byte) (raU : word) : Prop :=
  rw_cells asegs m (c_HA c) [C8 (c_ws c); C8 (c_wu c); C4 (Z_to_bv 64 (c_caplen c)); C4 (Z_to_bv 64 hlen)]
  /\ bytes_at asegs m (c_DA c) (zbytes d) /\ wr_at asegs m (c_DA c) (Z.of_nat (length d))
  /\ Forall (fun x => 0 <= x < 256)%Z d /\ length d = c_N c
  /\ mem_inv asegs m /\ munch (UW c spv) m0 m /\ wmono asegs m0 m
  /\ stk asegs m (c_lo c) (spv + -16)
  /\ rw_cells asegs m (spv + -16) [CB 8 j0; C8 raU]
  /\ unpoisoned m (c_HA c) (c_HA c + 24) /\ unpoisoned m (c_DA c) (c_DA c + Z.of_nat (c_N c)).

(* [comment removed for export] *)
Definition uhio (c : ppctx) (spv : Z) (m : mem) (d : list Z) (hlen : Z) : Prop :=
  rw_cells asegs m (c_HA c) [C8 (c_ws c); C8 (c_wu c); C4 (Z_to_bv 64 (c_caplen c)); C4 (Z_to_bv 64 hlen)]
  /\ bytes_at asegs m (c_DA c) (zbytes d) /\ wr_at asegs m (c_DA c) (Z.of_nat (length d))
  /\ Forall (fun x => 0 <= x < 256)%Z d /\ length d = c_N c
  /\ mem_inv asegs m /\ stk asegs m (c_lo c) spv
  /\ unpoisoned m (c_HA c) (c_HA c + 24) /\ unpoisoned m (c_DA c) (c_DA c + Z.of_nat (c_N c)).

Definition uhpost (c : ppctx) (m0 : mem) (ra spw s0 s1 s2 s3 : word) (hlen : Z) (d : list Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra spw (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
                  s3 (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
             (c_F c) (ret_pc ra) (c_fc c) None m' (seg_rom asegs)
    /\ munch (UW c (bv_unsigned spw)) m0 m' /\ wmono asegs m0 m' /\ uhio c (bv_unsigned spw) m' d hlen.

Ltac open_uh I :=
  destruct I as (HDR & ZB & ZW & ZR & LD & MI & MU & WM & ST & FRU & UNPH & UNPD);
  lazymatch type of ZB with bytes_at _ _ _ (zbytes ?d) =>
    let LZ := fresh "LZ" in pose proof (zbytes_length d) as LZ; rewrite LD in LZ end;
  unfold UW in MU.
Ltac close_uh := unfold uhinv, UW; repeat match goal with |- _ /\ _ => split end; first [hyp_by_addr | assumption | reflexivity].
(* [comment removed for export] *)
Ltac uh_ret :=
  do 2 lstep;
  lazymatch goal with FRU : rw_cells _ _ _ [CB 8 _; C8 _], ST : stk _ _ _ (?spv + -16) |- _ => release_frame FRU ST spv end;
  lstep;
  apply evtF_done; unfold uhpost, uhio, UW;
  repeat (lazymatch goal with |- ex _ => eexists end);
  split; [cbv delta [mkR]; reflexivity|];
  repeat match goal with |- _ /\ _ => split end; first [hyp_by_addr | assumption | reflexivity].
Ltac gsplitU x k :=
  let C := fresh "Hc" in
  destruct (Z.ltb_spec x k) as [C|C]; [bdecide; cbn [orb andb negb]; uh_ret | bdecide; cbn [orb andb negb]].
Local Ltac gsplitU_FF x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb]; uh_ret | bd_F; cbn [orb andb negb]].
Local Ltac gsplitU_FT x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb]; uh_ret | bd_T; cbn [orb andb negb]].
Local Ltac gsplitU_TF x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; uh_ret | bd_F; cbn [orb andb negb]].
Local Ltac gsplitU_TT x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; uh_ret | bd_T; cbn [orb andb negb]].
Local Ltac gsplitU__c1 x k :=
  let C := fresh "Hc" in
  destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; uh_ret | bd_F; cbn [orb andb negb]].
Local Ltac gsplitU__c2 x k :=
  let C := fresh "Hc" in
  destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; uh_ret | bd_F; cbn [orb andb negb]].
Local Ltac gsplitU__c3 x k :=
  let C := fresh "Hc" in
  destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; uh_ret | bd_F; cbn [orb andb negb]].
Local Ltac gsplitU__c4 x k :=
  let C := fresh "Hc" in
  destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; uh_ret | bd_F; cbn [orb andb negb]].
Local Ltac gsplitU__c5 x k :=
  let C := fresh "Hc" in
  destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; uh_ret | bd_F; cbn [orb andb negb]].
Local Ltac gsplitU__c6 x k :=
  let C := fresh "Hc" in
  destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; uh_ret | bd_F; cbn [orb andb negb]].
Local Ltac gsplitU__c7 x k :=
  let C := fresh "Hc" in
  destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; uh_ret | bd_F; cbn [orb andb negb]].
Local Ltac gsplitU__c8 x k :=
  let C := fresh "Hc" in
  destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; uh_ret | bd_F; cbn [orb andb negb]].
Local Ltac gsplitU__c9 x k :=
  let C := fresh "Hc" in
  destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; uh_ret | bd_F; cbn [orb andb negb]].
Local Ltac gsplitU__c10 x k :=
  let C := fresh "Hc" in
  destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; uh_ret | bd_F; cbn [orb andb negb]].
Local Ltac gsplitU__c11 x k :=
  let C := fresh "Hc" in
  destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; uh_ret | bd_F; cbn [orb andb negb]].
Local Ltac gsplitU__c12 x k :=
  let C := fresh "Hc" in
  destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; uh_ret | bd_F; cbn [orb andb negb]].
Local Ltac gsplitU__c13 x k :=
  let C := fresh "Hc" in
  destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; uh_ret | bd_F; cbn [orb andb negb]].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma swap_usb_isodescs_S : forall f nd cap i desc off d,
  swap_usb_isodescs (S f) nd cap i desc off d =
  if i <? nd then
    if cap <? off + 4 then d
    else if cap <? off + 4 + 4 then swap_field 4 desc d
    else if cap <? off + 4 + 4 + 4 then swap_field 4 (desc + 4) (swap_field 4 desc d)
    else swap_usb_isodescs f nd cap (i + 1) (desc + 16) (off + 4 + 4 + 4 + 4)
           (swap_field 4 (desc + 8) (swap_field 4 (desc + 4) (swap_field 4 desc d)))
  else d.
Proof. reflexivity. Qed.
#[using="Type"] Lemma swap_usb_isodescs_exit : forall f nd cap i desc off d,
  ((i <? nd) = false \/ (cap <? off + 4) = true) -> swap_usb_isodescs f nd cap i desc off d = d.
Proof. intros [|f] nd cap i desc off d H; [reflexivity|]. rewrite swap_usb_isodescs_S. destruct H as [-> | ->]; [reflexivity|]. destruct (i <? nd); reflexivity. Qed.

Definition uiso_spec__stmt : Prop := forall c, ppwf c -> forall (f : nat) (i : Z),
  forall (ra spw t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 t3 t4 t5 t6 : word) m0 m d (nd hlen : Z) j0 raU,
  uhinv c (bv_unsigned spw) m0 m d hlen j0 raU ->
  (c_lo c + 16 <= bv_unsigned spw <= bv_unsigned (c_sp c))%Z ->
  (16 * Z.of_nat f >= c_caplen c - (64 + 16 * i) + 12)%Z ->
  (0 <= i < nd)%Z -> (64 + 16 * i + 4 <= c_caplen c)%Z -> (0 <= nd < 2^32)%Z ->
  a0 = Z_to_bv 64 (c_DA c + (64 + 16 * i)) -> t1 = Z_to_bv 64 (c_DA c + (64 + 16 * i)) ->
  a7 = Z_to_bv 64 (Z.shiftr (c_DA c + (64 + 16 * i)) 3 + 2147450880) ->
  a1 = Z_to_bv 64 (bv_swrap 32 (64 + 16 * i + 20)) -> a2 = Z_to_bv 64 (c_caplen c) -> a3 = sx32 (Z_to_bv 64 nd) ->
  a4 = Z_to_bv 64 (i + 1) -> a5 = SBW -> a6 = Z_to_bv 64 65280 -> t0 = Z_to_bv 64 (-17) ->
  evtF asegs (c_RNG c) (uhpost c m0 raU spw s0 s1 s2 s3 hlen (swap_usb_isodescs f nd (c_caplen c) i (64 + 16 * i) (64 + 16 * i) d))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned spw + -16)) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             s3 (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x8a72c) (c_fc c) None m (seg_rom asegs)).
Section Sz3.
Variables c : ltac2:(SecDiet.SzSec.tyM 'uiso_spec__stmt "vhk" @c).
#[using="Type"] Lemma uiso_spec__body : ltac2:(SecDiet.SzSec.bodyP 'uiso_spec__stmt "vhk").
Proof.
  intros f WF.
 induction f as [|f IH]; intros i; intros until raU; intros I SPR FU IR CI ND -> -> -> -> -> -> -> -> -> ->.
  { exfalso. lia. }
  pose proof WF as WF'. open_wf WF. open_uh I.
  pose proof (bv_unsigned_in_range 64 (c_sp c)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (@ATOP_hi _) as ATOPhi.
  rewrite swap_usb_isodescs_S.
  replace (i <? nd) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (c_caplen c <? 64 + 16 * i + 4) with false by (symmetry; apply Z.ltb_ge; lia). simpl_if.
  ckp_at UNPD (c_DA c + (64 + 16 * i))%Z 4%Z. do 2 zstep. ck_cut 0x8a738%Z [11%Z].
  zstep. rd4 (64 + 16 * i)%Z. ck_cut 0x8a744%Z [29%Z]. ckp_clear.
  run. st4 (64 + 16 * i)%Z.
  run. rf_norm.
  destruct (Z.ltb_spec (c_caplen c) (64 + 16 * i + 8)) as [C1|C1].
  { bd_T. simpl_if. uh_ret. }
  bd_F. simpl_if.
  zstep. ckp_at UNPD (c_DA c + (64 + 16 * i) + 4)%Z 4%Z. do 3 zstep. ck_cut 0x8a788%Z [30%Z].
  zstep. rd4 (64 + 16 * i + 4)%Z. ck_cut 0x8a794%Z [30%Z]. ckp_clear.
  run. st4 (64 + 16 * i + 4)%Z.
  run. rf_norm.
  destruct (Z.ltb_spec (c_caplen c) (64 + 16 * i + 12)) as [C2|C2].
  { bd_T. simpl_if. uh_ret. }
  bd_F. simpl_if.
  zstep. ckp_at UNPD (c_DA c + (64 + 16 * i) + 8)%Z 4%Z. do 3 zstep. ck_cut 0x8a7d8%Z [30%Z].
  zstep. rd4 (64 + 16 * i + 8)%Z. ck_cut 0x8a7e4%Z [30%Z]. ckp_clear.
  run. st4 (64 + 16 * i + 8)%Z.
  bd_F.
  destruct (Z.ltb_spec (i + 1) nd) as [IN|IN]; cycle 1.
  { bd_T. rewrite swap_usb_isodescs_exit by (left; apply Z.ltb_ge; lia). uh_ret. }
  bd_F. run. rf_norm.
  destruct (Z.ltb_spec (c_caplen c) (64 + 16 * i + 20)) as [C5|C5].
  { bd_F. lstep. rewrite swap_usb_isodescs_exit by (right; apply Z.ltb_lt; lia). uh_ret. }
  bd_T.
  replace (64 + 16 * i + 16)%Z with (64 + 16 * (i + 1))%Z by lia.
  replace (64 + 16 * i + 4 + 4 + 4 + 4)%Z with (64 + 16 * (i + 1))%Z by lia.
  eapply (IH (i + 1)%Z); fastfirst (first [ noevar_assumption | close_uh | wordeq | lia
    | (f_equal; rewrite !Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia) ]).
Qed.
End Sz3.
#[using="Type"] Lemma uiso_spec : ltac:(let t := eval cbv delta [uiso_spec__stmt] in uiso_spec__stmt in exact t).
Proof. intros c WF f. ltac2:(SecDiet.SzSec.closeP 'uiso_spec__body "vhk"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition usbk (caplen : Z) (d : list Z) : list Z :=
  if caplen <? 52 then d else let d := swap_field 4 48 d in
  if caplen <? 56 then d else let d := swap_field 4 52 d in
  if caplen <? 60 then d else let d := swap_field 4 56 d in
  if caplen <? 64 then d else let d := swap_field 4 60 d in
  if get_u8 d 9 =? 0 then swap_usb_isodescs (Z.to_nat (caplen / 16 + 2)) (get_le32 d 60) caplen 0 64 64 d else d.

Definition usbtail_spec__stmt : Prop := forall c, ppwf c ->
  forall (ra spw t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 t3 t4 t5 t6 : word) m0 m d hlen j0 raU,
  uhinv c (bv_unsigned spw) m0 m d hlen j0 raU ->
  (c_lo c + 16 <= bv_unsigned spw <= bv_unsigned (c_sp c))%Z ->
  a0 = Z_to_bv 64 (c_HA c + 16) -> a1 = Z_to_bv 64 (c_DA c) -> a4 = Z_to_bv 64 (get_u8 d 9) -> a5 = SBW ->
  a6 = Z_to_bv 64 (Z.shiftr (c_HA c + 16) 3 + 2147450880) ->
  evtF asegs (c_RNG c) (uhpost c m0 raU spw s0 s1 s2 s3 hlen (usbk (c_caplen c) d))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned spw + -16)) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             s3 (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x8a584) (c_fc c) None m (seg_rom asegs)).
Section Sz4.
Variables c : ltac2:(SecDiet.SzSec.tyM 'usbtail_spec__stmt "v" @c).
#[using="Type"] Lemma usbtail_spec__body : ltac2:(SecDiet.SzSec.bodyP 'usbtail_spec__stmt "v").
Proof.
  intros WF; intros until raU; intros I SPR -> -> -> -> ->.
 pose proof WF as WF'. open_wf WF. open_uh I.
  pose proof (bv_unsigned_in_range 64 (c_sp c)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (@ATOP_hi _) as ATOPhi.
  unfold usbk.
  pose proof (get_u8_range d 9 ZR) as TT.
  ck0_at UNPH (c_HA c + 16)%Z; ck_go.
  do 2 lstep. rewrite (sx32_small (c_caplen _)) by lia. gsplitU__c1 (c_caplen c) 52%Z.
  zstep. ckp_at UNPD (c_DA c + 48)%Z 4%Z. do 3 zstep. ck_cut 0x8a5ac%Z [17%Z]. zstep. rd4 48%Z. ck_cut 0x8a5b8%Z [17%Z]. ckp_clear.
  run. st4 48%Z. kill_towers. gsplitU__c2 (c_caplen c) 56%Z.
  zstep. ckp_at UNPD (c_DA c + 52)%Z 4%Z. do 3 zstep. ck_cut 0x8a604%Z [17%Z]. zstep. rd4 52%Z. ck_cut 0x8a610%Z [17%Z]. ckp_clear.
  run. st4 52%Z. kill_towers. gsplitU__c3 (c_caplen c) 60%Z.
  zstep. ckp_at UNPD (c_DA c + 56)%Z 4%Z. do 3 zstep. ck_cut 0x8a65c%Z [17%Z]. zstep. rd4 56%Z. ck_cut 0x8a668%Z [17%Z]. ckp_clear.
  run. st4 56%Z. kill_towers. gsplitU__c4 (c_caplen c) 64%Z.
  zstep. ckp_at UNPD (c_DA c + 60)%Z 4%Z. do 3 zstep. ck_cut 0x8a6b4%Z [17%Z]. zstep. rd4 60%Z. ck_cut 0x8a6c0%Z [17%Z]. ckp_clear.
  run.
  name4 60%Z. st4 60%Z. fix_u8_all 9%Z.
  lazymatch goal with Hd : ?dn = swap_field 4 60 ?dold, EW : zslice 60 4 ?dold' = [?y0; ?y1; ?y2; ?y3] |- _ =>
    assert (ND : get_le32 dn 60 = (y3 + 256 * y2 + 65536 * y1 + 16777216 * y0)%Z)
      by (rewrite Hd; unfold swap_field; rewrite EW; cbn [rev app]; apply get_le32_write_same; lia);
    rewrite ND;
    pose proof (get_le32_of_slice _ _ _ _ _ _ EW) as EX
  end.
  lazymatch goal with EW : zslice 60 4 ?dold = [?y0; ?y1; ?y2; ?y3] |- _ =>
    match goal with |- context [Z_to_bv 64 ?E] =>
      lazymatch E with context [get_le32 dold 60] =>
        lazymatch E with Z.lor (Z.lor _ _) _ =>
          replace (Z_to_bv 64 E) with (sx32 (Z_to_bv 64 (y3 + 256 * y2 + 65536 * y1 + 16777216 * y0)%Z))
            by (rewrite <- (Z_to_bv_bv_unsigned (sx32 _)); f_equal;
                replace (y3 + 256 * y2 + 65536 * y1 + 16777216 * y0)%Z with (le_of_bytes [y3; y2; y1; y0]) by (cbn; lia);
                unfold get_le32; rewrite EW; repeat lanes_step; fastfirst (first [reflexivity | cbn [le_of_bytes]; lia]))
        end end end;
    assert (NDR : (0 <= y3 + 256 * y2 + 65536 * y1 + 16777216 * y0 < 2^32)%Z) by lia;
    set (nd := (y3 + 256 * y2 + 65536 * y1 + 16777216 * y0)%Z) in *
  end.
  lstep.
  lazymatch goal with |- context [get_u8 ?dd 9 =? 0] => esplit_FT (get_u8 dd 9) 0%Z end.
  2:{ uh_ret. }
  lstep. bd_F.
  rewrite EX.
  destruct (Z.eqb_spec nd 0) as [N0|N0].
  { bd_T. rewrite swap_usb_isodescs_exit by (left; apply Z.ltb_ge; lia). uh_ret. }
  bd_F. lstep.
  destruct (Z.ltb_spec (c_caplen c) 68) as [C68|C68].
  { bd_T. rewrite swap_usb_isodescs_exit by (right; apply Z.ltb_lt; lia). uh_ret. }
  bd_F. run.
  eapply (uiso_spec c WF' (Z.to_nat (c_caplen c / 16 + 2)) 0%Z); fastfirst (first [ noevar_assumption | close_uh | wordeq | lia
    | (f_equal; rewrite !Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia) ]).
Qed.
End Sz4.
#[using="Type"] Lemma usbtail_spec : ltac:(let t := eval cbv delta [usbtail_spec__stmt] in usbtail_spec__stmt in exact t).
Proof. intros c. ltac2:(SecDiet.SzSec.closeP 'usbtail_spec__body "v"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition usbhdr_spec__stmt : Prop := forall c, ppwf c -> forall (hl : bool)
  (ra spw t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 t3 t4 t5 t6 : word) m0 d hlen,
  uhio c (bv_unsigned spw) m0 d hlen -> artcells m0 ->
  (c_lo c + 16 <= bv_unsigned spw <= bv_unsigned (c_sp c))%Z ->
  a0 = Z_to_bv 64 (c_HA c) -> a1 = Z_to_bv 64 (c_DA c) -> a2 = Z_to_bv 64 (Z.b2z hl) ->
  evtF asegs (c_RNG c) (uhpost c m0 ra spw s0 s1 s2 s3 hlen (swap_linux_usb_header (mkHdr 0 0 (c_caplen c) hlen) d hl))
    (MS (mkR ra spw (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             s3 (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x8a1f0) (c_fc c) None m0 (seg_rom asegs)).
Section Sz5.
Variables c hl : ltac2:(SecDiet.SzSec.tyM 'usbhdr_spec__stmt "vhv" @c).
#[using="Type"] Lemma usbhdr_spec__body : ltac2:(SecDiet.SzSec.bodyP 'usbhdr_spec__stmt "vhv").
Proof.
  intros WF; intros until hlen; intros IO RT SPR -> -> ->.
 pose proof WF as WF'. open_wf WF.
  destruct IO as (HDR & ZB & ZW & ZR & LD & MI & ST & UNPH & UNPD).
  pose proof (zbytes_length d) as LZ. rewrite LD in LZ.
  pose proof (munch_refl (UW c (bv_unsigned spw)) m0) as MU. pose proof (wmono_refl asegs m0) as WM. unfold UW in MU.
  pose proof (bv_unsigned_in_range 64 (c_sp c)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (@ATOP_hi _) as ATOPhi.
  destruct RT as (_ & GOT & _ & _ & SHB & _).
  unfold swap_linux_usb_header. cbn [h_caplen h_len]. unfold URB_ISOCHRONOUS.
  carve_frame 16%nat ST.
  do 2 lstep.
  bd_F. lstep. bd_F.
  do 3 lstep.
  zstep. ck0 UNPH; ck_go.
  do 2 lstep. rewrite (sx32_small (c_caplen _)) by lia. gsplitU__c5 (c_caplen c) 8%Z.
  bd_F. lstep. bd_F.
  ckp_at UNPD (c_DA c) 1%Z. do 3 zstep. ck_cut 0x8a24c%Z [17%Z]. ckp_clear.
  zstep. ckp_at UNPD (c_DA c + 7)%Z 1%Z. do 3 zstep. ck_cut 0x8a260%Z [6%Z]. ckp_clear.
  ckp_at UNPD (c_DA c) 1%Z. zstep. rd4 0%Z. rd4 4%Z. ck_cut 0x8a270%Z [7%Z]. ckp_clear.
  ckp_at UNPD (c_DA c + 7)%Z 1%Z. zstep. ck_cut 0x8a278%Z [6%Z]. ckp_clear.
  run. st8 0%Z. kill_towers.
  ck0_at UNPH (c_HA c + 16)%Z; ck_go.
  do 2 lstep. rewrite (sx32_small (c_caplen _)) by lia. gsplitU__c6 (c_caplen c) 14%Z.
  zstep. ckp_at UNPD (c_DA c + 12)%Z 2%Z. do 3 zstep. ck_cut 0x8a314%Z [6%Z]. zstep. rd2 12%Z. ck_cut 0x8a320%Z [6%Z]. ckp_clear.
  run. st2 12%Z. kill_towers.
  gsplitU__c7 (c_caplen c) 24%Z.
  zstep. ckp_at UNPD (c_DA c + 16)%Z 1%Z. do 3 zstep. ck_cut 0x8a34c%Z [5%Z]. ckp_clear.
  zstep. ckp_at UNPD (c_DA c + 23)%Z 1%Z. do 3 zstep. ck_cut 0x8a360%Z [6%Z]. ckp_clear.
  ckp_at UNPD (c_DA c + 16)%Z 1%Z. zstep. rd4 16%Z. rd4 20%Z. ck_cut 0x8a370%Z [6%Z]. ckp_clear.
  zstep. ckp_at UNPD (c_DA c + 23)%Z 1%Z. do 3 zstep. ck_cut 0x8a384%Z [7%Z]. ckp_clear.
  run. st8 16%Z. kill_towers.
  ck0_at UNPH (c_HA c + 16)%Z; ck_go.
  do 2 lstep. rewrite (sx32_small (c_caplen _)) by lia. gsplitU__c8 (c_caplen c) 28%Z.
  zstep. ckp_at UNPD (c_DA c + 24)%Z 4%Z. do 3 zstep. ck_cut 0x8a420%Z [6%Z]. zstep. rd4 24%Z. ck_cut 0x8a42c%Z [6%Z]. ckp_clear.
  run. st4 24%Z. kill_towers. gsplitU__c9 (c_caplen c) 32%Z.
  zstep. ckp_at UNPD (c_DA c + 28)%Z 4%Z. do 3 zstep. ck_cut 0x8a478%Z [6%Z]. zstep. rd4 28%Z. ck_cut 0x8a484%Z [6%Z]. ckp_clear.
  run. st4 28%Z. kill_towers. gsplitU__c10 (c_caplen c) 36%Z.
  zstep. ckp_at UNPD (c_DA c + 32)%Z 4%Z. do 3 zstep. ck_cut 0x8a4d0%Z [6%Z]. zstep. rd4 32%Z. ck_cut 0x8a4dc%Z [6%Z]. ckp_clear.
  run. st4 32%Z. kill_towers. gsplitU__c11 (c_caplen c) 40%Z.
  zstep. ckp_at UNPD (c_DA c + 36)%Z 4%Z. do 3 zstep. ck_cut 0x8a528%Z [6%Z]. zstep. rd4 36%Z. ck_cut 0x8a534%Z [6%Z]. ckp_clear.
  run. st4 36%Z. kill_towers.
  ckp_at UNPD (c_DA c + 9)%Z 1%Z. do 2 zstep. ck_cut 0x8a578%Z [5%Z]. ckp_clear.
  rd1 9%Z.
  pose proof (get_u8_range d6 9 ZR) as TT.
  lazymatch goal with |- context [get_u8 ?dd 9 =? 0] => esplit_TF (get_u8 dd 9) 0%Z end.
  - lstep. gsplitU__c12 (c_caplen c) 44%Z.
    zstep. ckp_at UNPD (c_DA c + 40)%Z 4%Z. do 3 zstep. ck_cut 0x8a8b0%Z [6%Z]. zstep. rd4 40%Z. ck_cut 0x8a8bc%Z [6%Z]. ckp_clear.
    run. st4 40%Z. kill_towers.
    ck0_at UNPH (c_HA c + 16)%Z; ck_go.
    do 2 lstep. rewrite (sx32_small (c_caplen _)) by lia. gsplitU__c13 (c_caplen c) 48%Z.
    zstep. ckp_at UNPD (c_DA c + 44)%Z 4%Z. do 3 zstep. ck_cut 0x8a914%Z [6%Z]. zstep. rd4 44%Z. ck_cut 0x8a920%Z [6%Z]. ckp_clear.
    run. st4 44%Z. kill_towers.
    destruct hl; cbn [Z.b2z] in *.
    + bd_T.
      lazymatch goal with |- evtF ?s ?r (uhpost ?c0 ?mm ?ra0 ?sp0 ?x0 ?x1 ?x2 ?x3 ?hh ?E) ?st =>
        change (evtF s r (uhpost c0 mm ra0 sp0 x0 x1 x2 x3 hh (usbk (c_caplen c) d8)) st) end.
      eapply (usbtail_spec c WF'); fastfirst (first [ noevar_assumption | close_uh | wordeq | lia
        | (f_equal; fix_u8_all 9%Z; reflexivity) ]).
    + bd_F. uh_ret.
  - destruct hl; cbn [Z.b2z] in *.
    + bd_F.
      lazymatch goal with |- evtF ?s ?r (uhpost ?c0 ?mm ?ra0 ?sp0 ?x0 ?x1 ?x2 ?x3 ?hh ?E) ?st =>
        change (evtF s r (uhpost c0 mm ra0 sp0 x0 x1 x2 x3 hh (usbk (c_caplen c) d6)) st) end.
      eapply (usbtail_spec c WF'); fastfirst (first [ noevar_assumption | close_uh | wordeq | lia
        | (f_equal; fix_u8_all 9%Z; reflexivity) ]).
    + bd_T. uh_ret.
Qed.
End Sz5.
#[using="Type"] Lemma usbhdr_spec : ltac:(let t := eval cbv delta [usbhdr_spec__stmt] in usbhdr_spec__stmt in exact t).
Proof. intros c WF hl. ltac2:(SecDiet.SzSec.closeP 'usbhdr_spec__body "vhv"). Qed.

End CANSEC1.
