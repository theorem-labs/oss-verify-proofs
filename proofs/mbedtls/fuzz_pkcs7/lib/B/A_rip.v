(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT ARestrict A_exit_lib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Set Printing Width 200.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import LiaOrcFF5. (* [comment removed for export] *)
Local Ltac lia_t12 ::= orc_lia_t12. (* [comment removed for export] *)
Local Ltac ff5_rlia ::= orc_ff5_rlia. (* [comment removed for export] *)
Local Ltac ff5_overlap_ctx A2 n2 a len ::= orc_ff5_overlap_ctx A2 n2 a len. (* [comment removed for export] *)
Local Ltac ff5_overlap A2 n2 a len ::= orc_ff5_overlap A2 n2 a len. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_ff5_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 e25kn_keep_near (t : Init.constr) : Init.unit :=
  let seed := FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) t in
  let e := LiaTuning.zf_mkenv () in
  let (ids, _) := List.fold_left (fun acc h =>
      let (ids, cache) := acc in
      let (id, body, ty) := h in
      match body with
      | Init.Some _ => acc
      | Init.None =>
          let (isp, cache) := LiaTuning.zf_is_prop cache ty in
          if isp then
            (if LiaTuning.zf_plain_arith e ty then
               (if FSet.is_empty (FSet.inter seed (FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) ty))
                then (id :: ids, cache) else (ids, cache))
             else (id :: ids, cache))
          else (ids, cache)
      end) ([], { LiaTuning.zc_c := FMap.empty FSet.Tags.constant_tag; LiaTuning.zc_i := FMap.empty FSet.Tags.inductive_tag })
      (Control.hyps ()) in
  match ids with
  | [] => ()
  | _ :: _ => match Control.case (fun () => Std.clear ids) with
              | Init.Val _ => ()
              | Init.Err _ => List.iter (fun id => match Control.case (fun () => Std.clear [id]) with Init.Val _ => () | Init.Err _ => () end) ids
              end
  end.
Ltac ff_keep_near t ::= let f := ltac2:(t |- e25kn_keep_near (Option.get (Ltac1.to_constr t))) in f t.
Ltac2 gd_tbl_A_rip () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibA.ALazy.asan_layout"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.aok_addr"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.acc_ok"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.pair"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Walk.rip_consts"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "app_mem"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "Walk.m2s_post"; "Stdlib.ZArith.BinInt.Z.sub"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ov_read_bytes"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le8"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Corelib.Init.Logic.or"; "Walk.miz_post"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "Walk.app_range"; "Walk.rip_post"].


Notation SB := 0x7fff8000 (only parsing).
(* [comment removed for export] *)
Notation HSE := 0x10007fff7fff (only parsing).   (* [comment removed for export] *)
Notation HME := 0x7fffffffffff (only parsing).   (* [comment removed for export] *)
Definition app_mem (a : Z) : Prop := (0 <= a < SB) \/ (HSE < a <= HME).

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L2925329180.13 L63584205855.1300000;00QS1E1n2H02H1S1E1n2lo2hi2H22H31z2Hz". (* [comment removed for export] *)
Lemma acc_ok_aokZ : ltac2:(CDefT.buildp (gd_tbl_A_rip ()) "PL,$0.PCS,P,$1.SpPE,$1.Pn,$2.Plo,$1.Phi,$1.P,Px,$1.P,(3.(4.R3.R1.)(5.R1.R2.))(6.R8.R7.R2.)P,(4.=R5.)P,(5.R6.(7.+2.+40.))P,(4.R5.R7.)P,(4.(8.R8.(9.R7.))R5.)(:.R;.R:.(;.(<.(=.&40.)$2.)(>.(=.&40.)$2.(?.&40.R9.)R8.)(10.(<.(=.&40.)$2.))))")
(* [comment removed for export] *).
Proof.
  (intros L CS E n lo hi H H0 H1 H2 H3 z dd_H; ddestruct dd_H as (a & k & Hin & Hz)). destruct Hin as [Hin|[]]. injection Hin as <- <-.
  rewrite unsigned_lit in Hz by lia. apply H. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Ltac solve_acc_aok :=
  lazymatch goal with
  | |- acc_ok ?L ?CS [(Z_to_bv 64 ?E, ?n)] =>
      match goal with
      | H : forall x, ?lo <= x < ?hi -> aok_addr L CS x |- _ => eapply (acc_ok_aokZ L CS E n lo hi H); qlia
      end
  end.
(* [comment removed for export] *)
Ltac solve_acc1x := first [ first [ first [ solve_acc1 ] ] | solve_acc_aok ].
Ltac solve_acc ::=
  lazymatch goal with
  | |- acc_ok _ _ [] => apply acc_ok_nil
  | |- acc_ok _ _ [_] => solve_acc1x
  | |- acc_ok _ _ (?x :: _) => apply acc_ok_cons; [ solve_acc1x | solve_acc ]
  end.

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L5675691540.1300000JS2lo2hi1a1n2a'2n'2D12H12H2". (* [comment removed for export] *)
Lemma disjoint_from_sub : ltac2:(CDefT.buildp (gd_tbl_A_rip ()) "PW,(11.$12.)Pa,$1.Pn,$1.Pa',$1.Pn',$1.P,(13.R5.R4.R3.)P,(4.R5.R3.)P,(4.(8.R4.R3.)(8.R6.R5.))P,(4.=R4.)(13.R9.R6.R5.)")
(* [comment removed for export] *).
Proof.
  induction W as [|[lo hi] W IH]; intros a n a' n' D H1 H2 H3; cbn in D |- *; [exact I|].
  destruct D as [D1 D2]. split; [lia|]. eapply IH; eauto.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L30010285091.2L5744833530.2 000001007SS1x2Hx". (* [comment removed for export] *)
Lemma land_m8 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551608 = x - x mod 8.
Proof. intros x Hx. change 18446744073709551608 with (2^64 - 2^3). rewrite land_align_down by lia. reflexivity. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Lemma Z_to_bv_m1 : Z_to_bv 64 (-1) = Z_to_bv 64 18446744073709551615.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Hypothesis ASB : al_sb AL = SB.
  Hypothesis GSB : al_gsb AL = 0x1099f8.

  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Record rip_consts (m : mem) : Prop := {
    rc_got : ro_cells asegs m 0x0f5e50 [C8 (Z_to_bv 64 0x1099f8)];    (* [comment removed for export] *)
    rc_sb : ro_cells asegs m 0x1099f8 [C8 (Z_to_bv 64 SB)];           (* [comment removed for export] *)
    rc_gmid1 : ro_cells asegs m 0x0f5e58 [C8 (Z_to_bv 64 0x10a6e8)];
    rc_gmid2 : ro_cells asegs m 0x0f5e60 [C8 (Z_to_bv 64 0x10a6f0)];
    rc_ghigh : ro_cells asegs m 0x0f5e68 [C8 (Z_to_bv 64 0x10a6e0)];
    rc_mid1 : ro_cells asegs m 0x10a6e8 [C8 (Z_to_bv 64 0)];          (* [comment removed for export] *)
    rc_mid2 : ro_cells asegs m 0x10a6f0 [C8 (Z_to_bv 64 0)];          (* [comment removed for export] *)
    rc_high : ro_cells asegs m 0x10a6e0 [C8 (Z_to_bv 64 HME)]         (* [comment removed for export] *)
  }.

  (* [comment removed for export] *)
  Definition m2s_post (ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (a : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_rip ()) "Lms',$14.(15.(=.&40.)Lt0,(=.&40.)(15.(=.&40.)La1,(=.&40.)(15.(=.&40.)La2,(=.&40.)(15.(=.&40.)La3,(=.&40.)(15.(=.&40.)La4,(=.&40.)(15.(=.&40.)La5,(=.&40.)(15.(=.&40.)La6,(=.&40.)(15.(=.&40.)La7,(=.&40.)(16.$14.R9.(17.(18.O1:.O19.O18.O17.R8.O16.O15.O14.O13.(?.&40.(8.+7???8000.(19.O2.+8.)))R7.R6.R5.R4.R3.R2.R1.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.)O4.(1:.O1:.)O3.(1;.(=.&40.))O1.(1<.$1=.)))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00P0?L28910316587.55L29788642887.55L42959555860.55L52071667727.55L56769839783.55L59589536811.55L61576970358.55Q13309766199.55Q13662189053.55Q17926394621.55Q19186984375.55Q20075203965.55Q27138810167.55Q31400660535.55Q31567854903.55Q3519786423.55 Q41541228157.55Q43840475389.55Q44730802487.55Q46093812151.55Q51251745975.55Q53534663706.55Q55003169207.55Q5653862455.55 Q58779415165.55Q63043428221.55Q64151389367.55Q65177225725.55Q66713415735.55Q67803836087.55Q7769115319.55 Q9898984759.55 00000400800C00D00S00W00f00o01801A01J01S01T01U01^01_01h02102:02C02D02N02O02P02Y02b02k03403=03F03G03HS2raS2raS2ra1a4HIGHFS2ra1a3LOW4HIGHS2raS2ra1a3LOW4HIGHS2AL4IMG'S2AL4IMG'S2AL4IMG'S2AL4IMG'S2AL4IMG'SSS2AL4IMG'SS2AL4IMG'S2AL4IMG'S2AL4IMG'S2AL4IMG'SS2AL5ALWF'SSS2AL4IMG'S2AL4IMG'S2AL4IMG'S2AL4IMG'S2AL4IMG'S2AL4IMG'SS". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma m2s_spec : ltac2:(CDefT.buildp (gd_tbl_A_rip ()) "Pra,(=.&40.)Psp,(=.&40.)Pgp,(=.&40.)Ptp,(=.&40.)Pt0,(=.&40.)Pt1,(=.&40.)Pt2,(=.&40.)Ps0,(=.&40.)Ps1,(=.&40.)Pa0,(=.&40.)Pa1,(=.&40.)Pa2,(=.&40.)Pa3,(=.&40.)Pa4,(=.&40.)Pa5,(=.&40.)Pa6,(=.&40.)Pa7,(=.&40.)Ps2,(=.&40.)Ps3,(=.&40.)Ps4,(=.&40.)Ps5,(=.&40.)Ps6,(=.&40.)Ps7,(=.&40.)Ps8,(=.&40.)Ps9,(=.&40.)Ps10,(=.&40.)Ps11,(=.&40.)Pt3,(=.&40.)Pt4,(=.&40.)Pt5,(=.&40.)Pt6,(=.&40.)PF,(1>.&5.(=.&40.))Pfc,(=.&20.)Pm,P,(=.&40.)(1?.(=.&8.))Pa,$1.P,(20.R2.)P,(21.$1=.R3.)P,(22.R3.)P,(16.(=.&40.)R1=.(?.&40.R4.))P,(16.$1.(23.(24.&40.R27.)+2.)=)(25.$1=.VAL,VCS,(26.R28.R27.R26.R25.R23.R22.R21.R20.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R6.R7.)(17.(18.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.)R9.(?.&40.+6::58.)R8.(1;.(=.&40.))R7.(1<.$1=.)))")
(* [comment removed for export] *).
  Proof.
    intros until a. intros RC MI AM -> RA. al_facts. destruct RC as [RC1 RC2 RC3 RC4 RC5 RC6 RC7 RC8].
    (* [comment removed for export] *)
    do 8 zstep.
    change (Z.land ((Z.b2z (2147450880 <? 2147450879) + -1) mod 18446744073709551616) 2147450879) with 2147450879.
    destruct AM as [LOW | HIGH].
    - if_trueU. zstep. zstep. zstep.
      unfold m2s_post. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. finish.
    - if_falseU.
      (* [comment removed for export] *)
      do 8 zstep. rewrite Z_to_bv_m1. if_trueU.
      (* [comment removed for export] *)
      do 5 zstep. zstep. if_falseU. zstep. if_falseU. zstep. zstep. zstep.
      unfold m2s_post. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. finish.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section MIZ.
    Variables (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
    Variables (B E : Z).      (* [comment removed for export] *)
    Hypothesis Z0 : forall s, B <= s < E -> bytes_at asegs m s [Z_to_bv 8 0].
    Hypothesis AOK : forall x, B <= x < E -> aok_addr AL CS x.
    Hypothesis BE : 0 < B /\ B <= E /\ E + 16 < 2^64.
    Hypothesis MI : mem_inv asegs m.

    #[using="Z0"] Lemma rd0 : forall mx p, mx = m -> B <= p < E -> ov_read_bytes asegs mx (Z_to_bv 64 p) 1 = Some [Z_to_bv 8 0].
    Proof. intros mx p -> Hp. apply bytes_at_read1. apply Z0. exact Hp. Qed.

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00G0?L14209392534.56L23095723088.55L25322043201.55L2927488084.56 L2927568340.56 L30507073589.55L30507256230.55L35316742286.56L41533297073.56L46600584761.53L48936009005.56L53520132954.55L53520278217.55L53522230140.56L53522375420.56L54806006571.56L59685659453.48L61618252267.56Q21737369341.54Q35220444616.54Q4113165138.54 Q42751386428.54Q52326868281.5400000A00O00]01601O01k02K02\02o03E03P03i04B04[05405E07207=07N07O07d08408JS1E1k1p2AB2Hk3GE2S1k1p2AB2Hk2GES1k1p2AB2Hk2LTS1B1E2BE1k1p2AB2Hk2Hp3LT2S1B1E2BE1k1p2AB2Hk2Hp3HpES1B1E2BE1k1p2AB2Hk2Hp3HpE2GES1B1E2BE1k1p2AB2Hk2Hp3HpE3HAB2LTS1E1k1p2AB2Hk3LT2S1B1k1p2AB2Hk2Hp2LTS1B1E1k1p2AB2Hk2Hp3HpES1k1p2AB2HkS1B1E2BE1k1p2AB2Hk2Hp3HpES1B1E2BE1k1p2AB2Hk2Hp3HpES1B1E2BE1k1p2AB2Hk2Hp3LT2S1B1E2BE1k1p2AB2Hk2Hp3HpES1B1k1p2AB2Hk3HABS2AL2CS2sp2gp2tp2s02s12s22s32s42s52s62s72s82s93s103s111F2fc1m1B1E1p2ra2t02t12t22a62a72t32t42t52t62AB2AE2Hk2HpS1k1p2AB2HkS1E1k1p2AB2Hk3HpEFS1B1E2BE1k1p2AB2Hk2HpS1B1k1p2AB2Hk2HpS1B1E2BE1k1p2AB2Hk3HpE". (* [comment removed for export] *)
    #[using="IMG ALWF CSOK Z0 AOK BE"] Lemma miz_pro : ltac2:(CDefT.buildp (gd_tbl_A_rip ()) "Pk,$2.Pp,$1.Pra,(=.&40.)Pt0,(=.&40.)Pt1,(=.&40.)Pt2,(=.&40.)Pa6,(=.&40.)Pa7,(=.&40.)Pt3,(=.&40.)Pt4,(=.&40.)Pt5,(=.&40.)Pt6,(=.&40.)PAB,$1.PAE,$1.P,(4.(27.R2.R=.)(9.R>.))P,(3.(4.VB,R>.)(5.R>.R3.))P,(5.R?.VE,)P,(4.R5.(8.VB,+7.))(25.$1=.VAL,VCS,Lms',$14.(15.(=.&40.)La3',(=.&40.)(15.(=.&40.)La6',(=.&40.)(16.$14.R3.(17.(18.R13.Vsp,Vgp,Vtp,R12.R11.R10.Vs0,Vs1,(?.&40.VB,)(?.&40.=)(?.&40.R8.)R2.(?.&40.VE,)(?.&40.R9.)R1.R>.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R=.R<.R;.R:.)VF,(?.&40.+7:?>0.)Vfc,(1;.(=.&40.))Vm,(1<.$1=.)))))(17.(18.R10.Vsp,Vgp,Vtp,R?.R>.R=.Vs0,Vs1,(?.&40.VB,)(?.&40.=)(?.&40.R5.)(?.&40.(8.R11.+1.))(?.&40.VE,)(?.&40.R6.)R<.R;.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(?.&40.+7:?<8.)Vfc,(1;.(=.&40.))Vm,(1<.$1=.)))")
(* [comment removed for export] *).
    Proof.
      induction k as [|k IH]; intros p ra t0 t1 t2 a6 a7 t3 t4 t5 t6 AB AE Hk Hp HpE HAB; [lia|].
      al_facts.
      pose proof (rd0 m p eq_refl ltac:(lia)) as RD.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      destruct (Z_lt_le_dec (p + 1) AB) as [LT|GE].
      - if_falseU. zstep. zstep.
        destruct (Z_lt_le_dec (p + 1) E) as [LT2|GE2].
        + if_trueU. replace (p + 2) with ((p + 1) + 1) by lia. apply IH; lia.
        + if_falseU. finish.
      - if_trueU. finish.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L11343929457.36L13780811614.34L15045033905.35L39170549675.34L43108347413.37L55688794949.37L68057062556.3500000B00O00P00]00c00i00jS1B1E1q2H12H21i2HiS1B1E2BE1q2H2SS1B1E2BE1q2H1S1i2HiS1i2HiS". (* [comment removed for export] *)
    #[using="Z0 BE"] Lemma rd0_8 : ltac2:(CDefT.buildp (gd_tbl_A_rip ()) "Pmx,P,(=.&40.)(1?.(=.&8.))Pq,$1.P,(16.P,(=.&40.)(1?.(=.&8.))R2.Vm,)P,(4.VB,R2.)P,(4.(8.R3.+8.)VE,)(16.(1?.(11.(=.&8.)))(28.$1=.R5.(?.&40.R4.)#8.)(29.(11.(=.&8.))(2:.(?.&40.=))))")
(* [comment removed for export] *).
    Proof.
      intros mx q -> H1 H2. change (le8 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0) 8).
      assert (BA : bytes_at asegs m q (repeat (Z_to_bv 8 0) 8)).
      { split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
        ddestruct (Z0 (q + Z.of_nat i) ltac:(lia)) as (_ & _ & R). specialize (R 0%nat ltac:(cbn; lia)).
        rewrite Z.add_0_r in R. cbn [nth_error] in R. rewrite R.
        destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; try reflexivity. lia. }
      pose proof (bytes_at_read asegs m q _ 0 8 BA ltac:(lia) ltac:(cbn; lia)) as R. rewrite Z.add_0_r in R. exact R.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00F0?L17950387695.58L33417188756.58L36051661132.58L39578698653.55L39584927105.58L42076818871.55L43669344045.58L43669489342.58L46597059266.58L48418828696.58L55602584245.49L6023882209.58 L6024064114.58 L61024582381.54L61029219392.56L63369542573.55L67758745444.58Q18950560628.56Q26785554468.56Q39170186397.56Q42076844939.56Q7291830719.56 00000F00W00b01701E01U02102M02^02l04Z05605R05]05h06A06T06m07A07V07f07gS1B1k1q2AE2Hk2Hq2HM2Q8S1E1k1q2AE2Hk3HAES1k1q2AE2HkS1B1k1q2AE2Hk2Hq2HM1HS1k1q2AE2Hk2LTS1B1k1q2AE2Hk2HqS1B1E2BE1k1q2AE2Hk2Hq3HAE2Q8S1B1E2BE1k1q2AE2Hk2Hq3HAE2Q8S1k1q2AE2Hk2Q82GES1k1q2AE2Hk2GES2AL2CS2sp2gp2tp2s02s12s22s32s42s52s62s72s82s93s103s111F2fc1m1B1q2ra2t02t12t22a32a42a62a72t32t42t52t62AE2Hk2HqS1B1E2BE1k1q2AE2Hk2Hq3HAE2Q8S1B1E2BE1k1q2AE2Hk2Hq3HAE2Q8S1k1q2AE2HkS1k1q2AE2HkS1B1E1k1q2AE2Hk2Hq3HAE2Q8S1B1k1q2AE2Hk2Hq2LTS1B1E2BE1k1q2AE2Hk3HAE2Q8S1E1k1q2AE2Hk3HAE2Q8S1B1E2BE1k1q2AE2Hk2HqS1B1k1q2AE2Hk2HqF". (* [comment removed for export] *)
    #[using="IMG ALWF CSOK Z0 AOK BE"] Lemma miz_word : ltac2:(CDefT.buildp (gd_tbl_A_rip ()) "Pk,$2.Pq,$1.Pra,(=.&40.)Pt0,(=.&40.)Pt1,(=.&40.)Pt2,(=.&40.)Pa3,(=.&40.)Pa4,(=.&40.)Pa6,(=.&40.)Pa7,(=.&40.)Pt3,(=.&40.)Pt4,(=.&40.)Pt5,(=.&40.)Pt6,(=.&40.)PAE,$1.P,(4.(27.R1.R>.)(2;.+8.(9.R?.)))P,(3.(4.VB,R?.)(5.R?.R2.))P,(4.R3.VE,)P,(16.$1.(23.(27.R4.R11.)+8.)=)(25.$1=.VAL,VCS,Lms',$14.(15.(=.&40.)La3',(=.&40.)(16.$14.R2.(17.(18.R13.Vsp,Vgp,Vtp,R12.R11.R10.Vs0,Vs1,(?.&40.VB,)(?.&40.=)(?.&40.R7.)R1.R>.(?.&40.R7.)R=.R<.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R;.R:.R9.R8.)VF,(?.&40.+7:??4.)Vfc,(1;.(=.&40.))Vm,(1<.$1=.))))(17.(18.R11.Vsp,Vgp,Vtp,R10.R?.R>.Vs0,Vs1,(?.&40.VB,)(?.&40.=)(?.&40.R5.)R=.R<.(?.&40.R12.)R;.R:.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(?.&40.+7:?>4.)Vfc,(1;.(=.&40.))Vm,(1<.$1=.)))")
(* [comment removed for export] *).
    Proof.
      induction k as [|k IH]; intros q ra t0 t1 t2 a3 a4 a6 a7 t3 t4 t5 t6 AE Hk Hq HAE HM; [lia|].
      al_facts.
      assert (Q8 : q + 8 <= AE). { pose proof (Z.div_mod (AE - q) 8 ltac:(lia)). lia. }
      pose proof (rd0_8 m q eq_refl ltac:(lia) ltac:(lia)) as RD.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      pose proof (Z.div_mod (AE - q) 8 ltac:(lia)) as DM.
      destruct (Z_lt_le_dec (q + 8) AE) as [LT|GE].
      - if_trueU. apply IH; lia.
      - if_falseU. replace (q + 8) with AE by lia. finish.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L17284006785.47L36987104431.54L43640554336.54L44544551881.54L52065427221.54L52067411221.54L53516963345.54L53519250449.54L53973175886.54L54663237813.54L6530926777.52 Q13872711791.53Q3985286926.53 Q5367335784.53 Q54504742395.53Q59723228978.5300001`02302F02P02b03403>03H03Z03d04304B04Q04c055056S2AL2CS2sp2gp2tp2s02s12s22s32s42s52s62s72s82s93s103s111F2fc1m1B1E1r2ra2t02t12t22a02a32a52a62a72t32t42t52t62Hk2HrS1B1E1k1r2Hk2Hr3NE1S1B1E1k1r2Hk2Hr3NE1S1E1k1r2HkS1B1E2BE1k1r2Hk2HrS1B1E1k1r2Hk2Hr2E1S1E1k1r2HkS1E1k1r2HkS1B1E1k1r2Hk2Hr2E1S1E1k1r2HkS1B1E1k1r2Hk2HrS1B1E1k1r2Hk2HrS1B1E1k1r2Hk2HrS1B1E2BE1k1r2Hk2HrS1B1E2BE1k1r2Hk2HrF". (* [comment removed for export] *)
    #[using="IMG ALWF CSOK Z0 AOK BE"] Lemma miz_epi : ltac2:(CDefT.buildp (gd_tbl_A_rip ()) "Pk,$2.Pr,$1.Pra,(=.&40.)Pt0,(=.&40.)Pt1,(=.&40.)Pt2,(=.&40.)Pa0,(=.&40.)Pa3,(=.&40.)Pa5,(=.&40.)Pa6,(=.&40.)Pa7,(=.&40.)Pt3,(=.&40.)Pt4,(=.&40.)Pt5,(=.&40.)Pt6,(=.&40.)P,(4.(27.VE,R>.)(9.R?.))P,(3.(4.VB,R?.)(5.R?.VE,))(25.$1=.VAL,VCS,Lms',$14.(15.(=.&40.)La0',(=.&40.)(15.(=.&40.)La2',(=.&40.)(15.(=.&40.)La4',(=.&40.)(16.$14.R4.(17.(18.R13.Vsp,Vgp,Vtp,R12.R11.R10.Vs0,Vs1,R3.(?.&40.=)R2.R>.R1.R=.R<.R;.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(?.&40.+7;014.)Vfc,(1;.(=.&40.))Vm,(1<.$1=.))))))(17.(18.R?.Vsp,Vgp,Vtp,R>.R=.R<.Vs0,Vs1,R;.(?.&40.=)(?.&40.R10.)R:.(?.&40.(27.VE,R10.))R9.R8.R7.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R6.R5.R4.R3.)VF,(?.&40.+7;000.)Vfc,(1;.(=.&40.))Vm,(1<.$1=.)))")
(* [comment removed for export] *).
    Proof.
      induction k as [|k IH]; intros r ra t0 t1 t2 a0 a3 a5 a6 a7 t3 t4 t5 t6 Hk Hr; [lia|].
      al_facts.
      pose proof (rd0 m r eq_refl ltac:(lia)) as RD.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      destruct (Z.eq_dec (E - r) 1) as [E1|NE1].
      - if_falseU. finish.
      - if_trueU. replace (E - r + -1) with (E - (r + 1)) by lia. apply IH; lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  End MIZ.

  Definition miz_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m0 : mem)
      : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_rip ()) "Lms',$14.(15.(=.&40.)Lt0,(=.&40.)(15.(=.&40.)Lt1,(=.&40.)(15.(=.&40.)Lt2,(=.&40.)(15.(=.&40.)La1,(=.&40.)(15.(=.&40.)La2,(=.&40.)(15.(=.&40.)La3,(=.&40.)(15.(=.&40.)La4,(=.&40.)(15.(=.&40.)La5,(=.&40.)(15.(=.&40.)La6,(=.&40.)(15.(=.&40.)La7,(=.&40.)(15.(=.&40.)Lt3,(=.&40.)(15.(=.&40.)Lt4,(=.&40.)(15.(=.&40.)Lt5,(=.&40.)(15.(=.&40.)Lt6,(=.&40.)(15.P,(=.&40.)(1?.(=.&8.))Lm',P,(=.&40.)(1?.(=.&8.))(3.(16.$14.R10.(17.(18.O14.O13.O12.O11.R?.R>.R=.O10.O?.(?.&40.+1.)R<.R;.R:.R9.R8.R7.R6.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.R5.R4.R3.R2.)O4.(1:.O14.)O3.(1;.(=.&40.))R1.(1<.$1=.)))(3.(2<.(;.(<.$1.$1.)(>.$1.$1.(27.(24.&40.O13.)+10.)(24.&40.O13.))(10.(<.$1.$1.)))O1.R1.)(3.(2=.$1=.O1.R1.)(3.(21.$1=.R1.)(2>.$1=.R1.O2.(24.&40.O13.)))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L25203137715.17L3279566516.17 L68059074782.1700000:00D00ES1B1E1s2HsS1B1E1s2HsS". (* [comment removed for export] *)
  #[using="Type"] Lemma bytes0_transport : ltac2:(CDefT.buildp (gd_tbl_A_rip ()) "PW,(11.$12.)Pm,P,(=.&40.)(1?.(=.&8.))Pm',P,(=.&40.)(1?.(=.&8.))PB,$1.PE,$1.P,(2<.R5.R4.R3.)P,(13.R6.R3.(27.R2.R3.))P,Ps,$1.P,(3.(4.R5.R1.)(5.R1.R4.))(2?.$1=.R8.R2.(;.(=.&8.)(?.&8.=)(10.(=.&8.))))Ps,$1.P,(3.(4.R6.R1.)(5.R1.R5.))(2?.$1=.R8.R2.(;.(=.&8.)(?.&8.=)(10.(=.&8.))))")
(* [comment removed for export] *).
  Proof.
    intros W m m' B E MU D Z0 s Hs. eapply bytes_at_transport; [apply Z0; exact Hs | exact MU |].
    cbn [length]. eapply disjoint_from_sub; [exact D | lia | lia | lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01B0?L10702526323.78L14524292146.78L16568596277.77L20433961190.63L20936858519.74L21543076249.70L21552407279.77L2468607964.64 L25851966060.64L25852064106.74L2925490036.64 L2927488084.77 L2927488084.78 L2927568340.78 L30507073589.74L30507073589.77L30507256230.74L30507256230.77L31399144472.76L31399144472.77L31399144472.80L31627548657.77L32049487064.63L32049487064.77L32049487064.78L32049487064.81L33417188756.77L33419285938.78L33613964275.74L33613964275.77L33616061397.78L33766823662.78L35742629542.77L37785160196.77L3830262788.77 L3831913529.81 L3832538530.78 L38910070288.64L39123116247.77L39800437510.64L42630447157.74L42630447157.77L42630629798.74L42630629798.77L42852013956.63L43059266230.61L44086846542.74L46748113268.63L47654787572.63L47654787572.64L49097389315.74L5232386799.74 L53516695435.80L53517110800.77L53519091638.74L53519091638.76L54803909389.74L55443598204.77L6023882209.77 L6024064114.77 L6025979348.78 L6026161236.77 L6026161236.78 L61028697974.68L61028845559.69L61075828189.74L61400273446.74L63368182937.66L63368234669.67Q11801279589.67Q15640813018.81Q15641240641.78Q15643225575.77Q15643324129.63Q25513505925.66Q45914037331.64Q49698585326.65Q58146298210.66Q9841252130.78 Q9841684153.81 Q9843367298.63 Q9843465860.77 00000G00Y00j01101B01X01i02102?02S02e03703O04104R05005N05l06=06N06_07?07F07W07h08908M08_09709O09g0:<0:M0:g0;?0;W0;o0<30<J0<U0<m0=E0=]0>50>G0>U0>f0>m0??0?Q0?b0@30@;0@C0@Q0@Y0@m0A>0A_0BF0Bh0CD0Cf0D40DB0DS0Dd0E20E@0EV0Eg0F80FI0FP0Fi0G00GA0G^0H30HH0HS0HhS2ra1B1E2B02AB2AE2M22GES2ra1B1E2AB2AE3GE2S2ra1B1E2AB2AE2LTS2ra2spS2ra1B1E2B02AB2AES2ra2sp1B1E4DISJ2AB2AES2ra1B1E2AB2AE2LTS2ra1B1ES2ra1B1E2BE2SZS2ra1B1E2BE2SZ2AB2AES2ra1B1E2B02BE3E16S2ra1B1E2B02BE3E16S2ra1B1E2B02BE3E162AB2AES2ra1B1E2B02BE3E162AB2AE2M22D23GE2S2ra1B1E2B02BE3E162AB2AE2M12D12GES2ra1B1E2B02BE3E162AB2AE2M12D1S2ra1B1E2B02BE3E162AB2AE2D12LTS2ra1B1E2B02BE3E162AB2AE2M12D1S2ra2sp1B1E2AB2AES2ra2sp1B1E2AB2AES2ra2sp1B1E2AB2AES2ra1B1E2B02SZ2AB2AE2M12M22D12D2S2ra2spS2ra2sp1B1E2AB2AES2ra2sp1B1E2AB2AES2ra2sp1B1E2AB2AES2ra1B1E2B02BE2AB2AES2ra1B1E2AB2AE3LT2S2ra1B1E2B02BE3E162AB2AES2ra1B1E2B02BE3E162AB2AES2ra1B1E2B02BE3E162AB2AES2ra1B1E2AB2AE2GE3LT2S2ra1B1E2AB2AE2GES2ra1B1E2B02BE2AB2AE2M12LTS2ra2sp1B1E2lo3SPL2AB2AES2ra2sp1B1E2lo3SPL2AB2AES2ra2sp1B1E2lo3SPL2AB2AES2raS2ra1B1E2B02BE2AB2AE2LTS2ra1B1E2SZS2ra1B1E2B02BE3E162AB2AES2ra1B1E2B02BE3E162AB2AES2ra1B1E2B02BE3E162AB2AES2ra1B1E2B02BE3E162AB2AES2ra1B1E2B02BE3E16S2ra2sp2lo3SPLS2ra1B1E2AB2AE2LTS2ra2spS2ra1B1E2B02BE3E16S2ra1B1E2B02BE3E16S2ra1B1E2AB2AE2LTS2ra1B1E2BE2AB2AES2ra1B1ES2ra1B1ES2ra1B1E2AB2AES2ra1B1ES2ra1B1E2B02BE2AB2AES2ra1B1E2AB2AE2GES2ra1B1E2B02BE3E162AB2AE2M22D22GES2ra1B1E2B02BE3E162AB2AE2M22D22LT2M12D1S2ra1B1E2B02BE3E162AB2AE2M22D23GE2S2ra1B1E2B02BE3E162AE2GE3LT2S2ra1B1E2B02BE3E162AB2AE2D22GE3LT2S2ra1B1E2AB2AES2ra1B1E2AB2AES2ra1B1E2AB2AE2GES2ra1B1E2BE2AB2AES2ra1B1E2AB2AES2ra1B1E2AB2AES2ra2sp2HB5Ha_st5Hl_stS2sp1B1E2lo2AB2AES2sp1B1E2lo2AB2AES2sp1B1E2lo2AB2AES2sp2loS2ra2sp2lo2HB5Ha_st5Hl_stS2sp2HBS2sp3SPR2HB5Ha_stS2ra2sp2lo3SPL2HB5Ha_st5Hl_stS2sp1B1E2lo3SPL2AB2AES2sp1B1E2lo3SPL2AB2AES2sp2lo3SPLS2sp1B1E2lo3SPL2AB2AE". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma miz_spec : ltac2:(CDefT.buildp (gd_tbl_A_rip ()) "Pra,(=.&40.)Psp,(=.&40.)Pgp,(=.&40.)Ptp,(=.&40.)Pt0,(=.&40.)Pt1,(=.&40.)Pt2,(=.&40.)Ps0,(=.&40.)Ps1,(=.&40.)Pa0,(=.&40.)Pa1,(=.&40.)Pa2,(=.&40.)Pa3,(=.&40.)Pa4,(=.&40.)Pa5,(=.&40.)Pa6,(=.&40.)Pa7,(=.&40.)Ps2,(=.&40.)Ps3,(=.&40.)Ps4,(=.&40.)Ps5,(=.&40.)Ps6,(=.&40.)Ps7,(=.&40.)Ps8,(=.&40.)Ps9,(=.&40.)Ps10,(=.&40.)Ps11,(=.&40.)Pt3,(=.&40.)Pt4,(=.&40.)Pt5,(=.&40.)Pt6,(=.&40.)PF,(1>.&5.(=.&40.))Pfc,(=.&20.)Pm,P,(=.&40.)(1?.(=.&8.))PB,$1.PE,$1.Plo,$1.P,Ps,$1.P,(3.(4.R4.R1.)(5.R1.R3.))(2?.$1=.R6.R2.(;.(=.&8.)(?.&8.=)(10.(=.&8.))))P,Px,$1.P,(3.(4.R5.R1.)(5.R1.R4.))(6.VAL,VCS,R2.)P,(5.=R5.)P,(5.R6.R5.)P,(5.(8.R6.+10.)(7.+2.+40.))P,(21.$1=.R9.)P,(16.(=.&40.)R22.(?.&40.R9.))P,(16.(=.&40.)R22.(?.&40.(27.R9.R:.)))P,(4.(27.R:.R;.)(7.+2.+28.))P,(2>.$1=.R=.R:.(24.&40.R2=.))P,(4.=R;.)P,(4.R<.(27.(24.&40.R2?.)+10.))P,(30.VCS,R=.(27.(24.&40.R30.)R=.))P,(31.(4.R?.(27.(24.&40.R31.)+10.))(4.(24.&40.R31.)R10.))P,(16.$1.(23.(24.&40.R33.)+2.)=)(25.$1=.VAL,VCS,(32.R34.R33.R32.R31.R2=.R2<.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R15.R14.R10.R13.)(17.(18.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.)R15.(?.&40.+7:?88.)R14.(1;.(=.&40.))R13.(1<.$1=.)))")
(* [comment removed for export] *).
  Proof.
    intros until lo. intros Z0 AOK B0 BE E16 MI -> -> SZ ST LO0 SPL SCS DISJ RA. al_facts.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat ST.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. if_falseU.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    replace (B + (E - B)) with E by lia. rewrite !land_m8 by lia.
    set (AB := B + 7 - (B + 7) mod 8). set (AE := E - E mod 8).
    pose proof (Z.mod_pos_bound (B + 7) 8 ltac:(lia)) as M1. pose proof (Z.mod_pos_bound E 8 ltac:(lia)) as M2.
    pose proof (Z.div_mod (B + 7) 8 ltac:(lia)) as D1. pose proof (Z.div_mod E 8 ltac:(lia)) as D2.
    assert (Z1 : forall s, B <= s < E -> bytes_at asegs m0 s [Z_to_bv 8 0]).
    { eapply bytes0_transport; [exact MU | cbn; lia | exact Z0]. }
    (* [comment removed for export] *)
    assert (T2 : forall (t0' a3' a5' a6' a7' : word),
      evtA asegs AL CS (miz_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 B) (Z_to_bv 64 0) (Z_to_bv 64 AE) a3' (Z_to_bv 64 E) a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x7aff4) fc None m0 (seg_rom asegs))).
    { intros t0' a3' a5' a6' a7'.
      (* [comment removed for export] *) zstep.
      destruct (Z_lt_le_dec AE B) as [LT|GE].
      - if_trueU. zstep. zstep. zstep. zstep. release_frame FR ST (bv_unsigned sp). finish.
      - if_falseU. (* [comment removed for export] *) zstep.
        destruct (Z_lt_le_dec AE E) as [LT2|GE2].
        + if_falseU. zstep.
          eapply evtA_cut; [eapply (miz_epi (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 B E Z1 AOK) with (k := 8%nat); cbn [Z.of_nat]; lia
                           | cbn beta; (intros ms' dd_H; ddestruct dd_H as (a0' & a2' & a4' & ->))].
          zstep. zstep. zstep. zstep. release_frame FR ST (bv_unsigned sp). finish.
        + if_trueU. zstep. zstep. zstep. zstep. release_frame FR ST (bv_unsigned sp). finish. }
    (* [comment removed for export] *)
    assert (T1 : forall (t0' a3' a6' a7' : word),
      evtA asegs AL CS (miz_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 B) (Z_to_bv 64 0) (Z_to_bv 64 AE) a3' (Z_to_bv 64 E) (Z_to_bv 64 AB) a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x7afe0) fc None m0 (seg_rom asegs))).
    { intros t0' a3' a6' a7'.
      (* [comment removed for export] *) zstep.
      destruct (Z_lt_le_dec AB AE) as [LT|GE].
      - if_falseU.
        eapply evtA_cut; [eapply (miz_word (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 B E Z1 AOK) with (k := Z.to_nat (2^40)); lia
                         | cbn beta; intros ms' (a3'' & ->)].
        apply T2.
      - if_trueU. apply T2. }
    (* [comment removed for export] *)
    zstep.
    destruct (Z_lt_le_dec B AB) as [LT|GE].
    - if_falseU. (* [comment removed for export] *) zstep. if_falseU. zstep. zstep.
      eapply evtA_cut; [eapply (miz_pro (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 B E Z1 AOK) with (k := 8%nat); cbn [Z.of_nat]; lia
                       | cbn beta; (intros ms' dd_H; ddestruct dd_H as (a3'' & a6'' & ->))].
      apply T1.
    - if_trueU. apply T1.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition app_range (lo hi : Z) : Prop := (0 < lo /\ hi < SB) \/ (HSE < lo /\ hi <= HME).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L2582033976.22 L46215616233.24L51402805101.26L59308582510.27L61028787377.20L61028792521.26L61028845559.21L9252946190.26 00000R01501>01N01U01^01e01nS3BEG2gb2ge2H12Hb2He2H01s2Hs2D12D2S3BEG1n2gb2ge2H12H22He2H01s2D21g2HgS2gb2ge1sS2gb2ge1s1g1k2HKS2gb2geS2gb2ge1sS2gb2geS2gb2ge1s". (* [comment removed for export] *)
  #[using="ASB"] Lemma aobj_shadow_zero_range : ltac2:(CDefT.buildp (gd_tbl_A_rip ()) "Pm,P,(=.&40.)(1?.(=.&8.))PBEG,$1.Pn,$1.Pgb,$1.Pge,$1.P,(33.$1=.VAL,VCS,R5.R4.R3.)P,(4.R5.R3.)P,(4.R3.(8.R6.R5.))P,(16.$1.(23.R5.+8.)=)P,(16.$1.(23.R5.+8.)=)P,(4.=R9.)Ps,$1.P,(3.(4.(8.+7???8000.(19.R9.+8.))R1.)(5.R1.(8.+7???8000.(19.R8.+8.))))(2?.$1=.R=.R2.(;.(=.&8.)(?.&8.=)(10.(=.&8.))))")
(* [comment removed for export] *).
  Proof.
    intros m BEG n gb ge OBJ H1 H2 Hb He H0 s Hs.
    destruct OBJ as [_ SH].
    pose proof (Z.div_mod gb 8 ltac:(lia)) as D1. pose proof (Z.div_mod ge 8 ltac:(lia)) as D2.
    set (g := 8 * (s - SB)).
    assert (Hg : gb <= g /\ g + 8 <= ge) by (subst g; lia).
    ddestruct (SH (g + 7) ltac:(lia)) as (k & B & HK).
    replace (shadow_of AL (g + 7)) with s in B.
    2:{ unfold shadow_of. rewrite ASB. subst g. replace (8 * (s - 2147450880) + 7) with (7 + (s - 2147450880) * 8) by lia.
        rewrite Z.div_add by lia. change (7 / 8) with 0. lia. }
    replace (Z_to_bv 8 0) with k; [exact B|].
    apply bv_eq. change (bv_unsigned (Z_to_bv 8 0)) with 0.
    destruct HK as [HK|HK]; [exact HK|]. exfalso.
    replace ((g + 7) mod 8) with 7 in HK; [lia|]. subst g.
    replace (8 * (s - 2147450880) + 7) with (7 + (s - 2147450880) * 8) by lia. rewrite Z.mod_add by lia. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition rip_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_rip ()) "Lms',$14.(15.(=.&40.)Lt0,(=.&40.)(15.(=.&40.)Lt1,(=.&40.)(15.(=.&40.)Lt2,(=.&40.)(15.(=.&40.)La1,(=.&40.)(15.(=.&40.)La2,(=.&40.)(15.(=.&40.)La3,(=.&40.)(15.(=.&40.)La4,(=.&40.)(15.(=.&40.)La5,(=.&40.)(15.(=.&40.)La6,(=.&40.)(15.(=.&40.)La7,(=.&40.)(15.(=.&40.)Lt3,(=.&40.)(15.(=.&40.)Lt4,(=.&40.)(15.(=.&40.)Lt5,(=.&40.)(15.(=.&40.)Lt6,(=.&40.)(15.P,(=.&40.)(1?.(=.&8.))Lm',P,(=.&40.)(1?.(=.&8.))(3.(16.$14.R10.(17.(18.O14.O13.O12.O11.R?.R>.R=.O10.O?.(?.&40.=)R<.R;.R:.R9.R8.R7.R6.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.R5.R4.R3.R2.)O4.(1:.O14.)O3.(1;.(=.&40.))R1.(1<.$1=.)))(3.(2<.(;.(<.$1.$1.)(>.$1.$1.O2.(24.&40.O13.))(10.(<.$1.$1.)))O1.R1.)(3.(2=.$1=.O1.R1.)(3.(21.$1=.R1.)(2>.$1=.R1.O2.(24.&40.O13.)))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "04Z0@L10891492106.96 L11123517328.1  L12283411672.110L12283411672.68 L12283411672.69 L12283411672.96 L13301871092.69 L14106684376.110L14106684376.68 L14106684376.96 L17587896041.100L17646078182.68 L17747144802.98 L17751112592.1  L1918478778.1   L19892441013.1  L24417571617.0  L25589954286.89 L27198631884.70 L2841052340.108 L2846022074.1   L28923334834.88 L28923334834.89 L29430633167.96 L2956786794.65  L30065961188.99 L30066199982.89 L30068886702.100L30068886702.95 L30284306320.1  L30786468673.96 L30786646738.95 L30786646738.96 L30985251090.96 L31118484991.96 L31700123578.1  L34056468398.89 L34282961881.100L3521825151.96  L35265264016.1  L35523438353.89 L36425864855.96 L36425882626.68 L36438237060.110L38236262928.96 L38495852400.96 L39188636933.0  L39593809371.98 L39843640889.96 L39887139444.69 L40032950175.98 L41288976216.110L41288976216.68 L41288976216.69 L41288976216.96 L41558151098.1  L43059592457.66 L43082027553.2  L43884290764.96 L44866992728.110L44866992728.68 L44866992728.69 L44866992728.96 L45898055924.69 L46229568912.1  L46279744166.80 L47302871662.3  L47768637023.108L48429268312.110L48429268312.68 L48429268312.69 L48429268312.96 L49345641752.67 L49345641752.95 L49358208408.109L50029270778.100L50029270778.99 L50830822330.1  L5145216728.110 L5145216728.68  L5145216728.69  L5145216728.96  L51925114228.69 L52065658262.93 L52067165334.88 L52067434972.97 L5259631286.116 L52655779862.100L52655779862.99 L52658204950.89 L52677338938.89 L53519057080.70 L53519189168.68 L53579518934.96 L54057340867.98 L54316131131.98 L54422382992.1  L54614395357.82 L55125139816.98 L55651989946.1  L57564295610.1  L57933933556.69 L59577422002.88 L60662689184.98 L61028697974.76 L61028786748.98 L61028845430.78 L61028845559.77 L61030615024.116L61929719224.70 L61947803659.96 L63368120110.79 L63368234669.75 L63370211065.74 L63962036340.68 L64788204432.1  L66286785511.2  L68354046352.1  L68506922624.100L7274816372.69  L828632639.89   L8722184664.110 L8722184664.68  L8722184664.69  L8722184664.96  L8926070878.95  L8926070878.96  L8926249421.96  L9036480958.98  L913420218.1    L9522996899.98  N35583862102.116N39242030976.116O11439213320.115O12062710536.115O19004160776.115O20618136072.115O2453481106.115 O30985873160.115O40551007240.115O66031421960.115O7754886152.115 P11136886036.72 P11136886036.73 P17762908436.72 P17762908436.73 P1922136926.115 P2842299230.115 P30297150740.72 P30297150740.73 P31703805278.115P35252419348.72 P35252419348.73 P41570262366.115P46232977172.72 P46232977172.73 P50818718046.115P54410586900.72 P54410586900.73 P55663995742.115P57576366942.115P64783223060.72 P64783223060.73 P68366891796.72 P68366891796.73 P918125918.115  Q12646246347.98 Q1321491137.89  Q1324309441.96  Q13265963961.89 Q13314135726.89 Q13518542596.100Q13666290020.89 Q15395347769.89 Q15457446739.69 Q15457446739.70 Q15643324129.68 Q15643337844.96 Q15647878503.110Q15930096381.100Q15930096381.98 Q17566570372.99 Q17930153572.89 Q18361895783.110Q18365907572.96 Q18365925601.68 Q18365925601.69 Q19109331493.97 Q19112230296.94 Q19182999854.89 Q20071068132.89 Q20179087425.89 Q21800371641.89 Q21879630871.96 Q21879645826.68 Q21879645826.69 Q21892523268.110Q24400136438.94 Q24443213121.89 Q25513505925.71 Q25513505925.72 Q26267358981.98 Q27134926254.89 Q27907200258.68 Q27907200258.69 Q27907219351.96 Q27911231108.110Q2957925441.89  Q30985251090.96 Q31396950702.89 Q31563202990.89 Q31834646913.115Q32655486836.96 Q32655500769.68 Q32655500769.69 Q32659924583.110Q32829662242.97 Q33139991988.96 Q33141299721.99 Q33913700356.110Q33918256002.68 Q33918256002.69 Q33918273815.96 Q3507278126.89  Q36721272633.96 Q36723828281.89 Q3830427394.68  Q3830427394.69  Q3830441367.96  Q3834260612.110 Q39593792729.100Q39830861497.115Q39935065476.110Q39939554818.68 Q39939554818.69 Q39939568791.96 Q41139448935.110Q41152393185.68 Q41152393185.69 Q41152406900.96 Q41553734372.89 Q43278597817.89 Q43611253674.94 Q43611253674.96 Q43790089409.89 Q43853540452.89 Q43854916964.96 Q44648825076.96 Q44648843873.68 Q44648843873.69 Q44652743143.110Q44743695790.89 Q45411106873.89 Q46097546542.89 Q47296093069.97 Q48054079937.89 Q49698585326.70 Q49698585326.71 Q51223049447.110Q51235796833.68 Q51235796833.69 Q51235814900.96 Q51238725678.89 Q51241543982.96 Q51814369660.96 Q53519735171.96 Q53522290819.89 Q55007690030.89 Q5640840366.89  Q58774900452.89 Q59830194919.110Q59843124212.96 Q59843137889.68 Q59843137889.69 Q60499890873.89 Q63038890980.89 Q64147683374.89 Q65164473700.89 Q65275246017.89 Q66289047267.99 Q66522067074.68 Q66522067074.69 Q66522085911.96 Q66534486788.110Q66717387950.89 Q66904668473.89 Q67405006657.89 Q67528989526.72 Q67528989526.73 Q67805123374.96 Q67807941166.89 Q7377275490.71  Q7377275490.72  Q7781758510.89  Q9838812676.110 Q9843349271.96  Q9843367298.68  Q9911269806.89  00000@00A00K00O00S00]00a00k00o01901E01I01R01S01T01X01Y01`01h01o02002702>02L02V02b03703C03O03P04304h05]06906I06J06X07I08=08>08N08_08j09;09E0:10:20:<0:M0:Q0;?0;I0;M0;Q0;[0;\0;g0;h0<50<?0<C0<G0<Q0<U0<V0<l0<m0=P0=Z0=^0=b0=l0>00>:0>D0>P0>\0>]0>g0>k0>o0?90?=0?n0?o0@`0@g0AG0Ag0BP0B`0Ba0Bb0C=0D10D_0D`0EG0F>0F?0F@0FD0FK0G90G@0GG0GN0GU0G\0Ga0HB0HI0HP0HW0H[0H\0H]0H^0IC0IG0IS0I]0Ia0Ie0Io0J^0KM0L;0L`0La0MR0Mb0N<0N=0N>0N?0N@0NK0NL0NM0NN0NO0O00O`0PA0Q10QI0Qa0RB0S20SJ0Sk0T[0U30UT0VD0V\0W=0Wm0XE0X]0Y>0Yn0ZO0[?0[W0[^0[_0[`0[a0\70\>0\M0\N0\U0\\0\c0]00]=0]D0]K0]W0]f0^30^@0^G0^N0^Z0^f0_<0_K0_L0_M0_^0_i0`40`E0`L0`M0`f0aN0b?0bF0bQ0b\0bm0c>0c?0c[0cb0d80dE0dR0dY0d`0dm0e40e;0eB0eS0e^0ei0f:0fA0fB0fC0fN0fY0fj0g;0gE0gV0gg0h20h=0hN0h[0hb0hi0i60iE0iF0iM0iT0iU0id0j30j@0jG0jN0j[0k10k20kH0km0kn0l?0lP0l]0ld0lk0m80m?0mF0mR0mb0n20n90n@0nO0n\0ni0o00o70o80oG0o]0ol0om10R10]10h11911J11\11]11^12;12g13913K13h14T14[14l15=15H15OS3BEG1n2qb2qe2GEFS2sp3BEG1nS2spS2spS2sp3BEG1nS2spS2sp3BEG1nS2spS2sp3BEG1nS3BEG1n1N2NZS2spS3BEG1n1xFFS2spSS3BEG1nS1n1N2NZS3BEG1nFS3BEG1nS3BEG1nS3BEG1n2lo3LO0S3BEG1n2ARS3BEG1n1N2B0S3BEG1n1N3LOW4HIGH2B0S3BEG1n1N2B0S3BEG1n1N2B0FS3BEG1n1N2B02ab3Eab2M12D02M02qb3HqbS3BEG1n2B02ab2ae3Eab3Eae2M12M22D02M02qb3Hqb2qe3Hqe2LTS3BEG1n2B02ab2ae3Eab3Eae2M12M22D02M02qb3Hqb2qe3Hqe2LTS2sp3BEG1n2lo3LO03SPL3SPR2B0S3BEG1n2qb2qe2LTFS3BEG1n1N4HIGHS3BEG1n1N2AR2B02NZ2ab2ae3Eab3Eae2D22qb3Hqb2qe3HqeS3BEG1n1N2B02ab2ae3Eab3Eae2M12M22D02M02qb3Hqb2qe3HqeFS3BEG1n1N3LOW2B0S2sp3BEG1n2lo3SPLS2sp2lo3SPLS2sp3BEG1n2lo3SPLS3BEG1n2loS2sp3BEG1n2lo3LO03SPL2B02ae3Eae2M22qb2qe3HqeSS3BEG1n2B0S2sp3BEG1n2lo3SPLS2spS3BEG1n2B02ab2ae3Eab3Eae2D12qb3Hqb2qe3Hqe1x2HxS2sp3BEG1nS2spS2spS2sp3BEG1nFS2sp2lo3SPLFS2sp3BEG1n2loS2sp3BEG1nS2spS2spS2sp3BEG1nS2spFS3BEG1n1N2B02ab3Eab2D1FS3BEG1n1N2AR2B02NZ2ae3Eae2D22qe3HqeS2sp3BEG1nS2spS2spS2sp3BEG1nS2spS2sp3BEG1nS2sp3BEG1nS3BEG1n1N2B0S3BEG1n1N2B0FS2sp3BEG1nS2spS2spS2sp3BEG1nS2spS3BEG1n1N2B02ab2ae3Eab3Eae2M12M22D22qb3Hqb2qe3HqeFS3BEG1n1N2B02ab2ae3Eab3Eae2M12M22D22qb3Hqb2qe3HqeS3BEG1nS3BEG1n1N2B02ae3Eae2M22D22qe3HqeS3BEG1n1N2B02ae3Eae2M22D22qe3HqeS3BEG1n1N3LOW2B02ae3Eae2M22D22qe3Hqe4HIGHS3BEG1n3LOW4HIGHSSS3BEG1n2B02ae3Eae2M22qe3HqeS3BEG1n2B02ab2ae3Eab3Eae2M12M22D12qb3Hqb2qe3Hqe1x2HxS3BEG1n2B02ab2ae3Eab3Eae2D12qb3Hqb2qe3Hqe1x2HxFS3BEG1n1N2B02ab2ae3Eab3Eae2M12D22qb3HqbS3BEG1n2B02ab2ae3Eab3Eae2M12M22D12D22qb3Hqb2qe3Hqe1x2HxFFS2spS3BEG1nS3BEG1n2B02ab2ae3Eab3Eae2D12qb3Hqb2qe3Hqe1x2HxS3BEG1nS3BEG1nS3BEG1nS3BEG1nS3BEG1nS1n1NS3BEG1n2B02ab3Eab2M12D02M02qb3HqbS3BEG1nS3BEG1nS3BEG1nS2spFFFS2AL3ASB3BEG1n2B02ae3Eae2M22D22qe3HqeS2spS3BEG1n4HIGHS2sp3BEG1nS2spS2spS2sp3BEG1nS3BEG1n2B02ab2ae3Eab3Eae2M22D12qb3Hqb2qe3Hqe2LTS3BEG1n2B02ab2ae3Eab3Eae2M22D12qb3Hqb2qe3Hqe2LTS3BEG1n1N2B02ab2ae3Eab3Eae2M22qb3Hqb2qe3Hqe2GES2AL3ASB3BEG1n2B02ae3Eae2M22D22qe3HqeFS3BEG1n2B02ab2ae3Eab3Eae2M22D12qb3Hqb2qe3Hqe1x2HxS2sp3BEG1n3x141CS2sp3BEG1n2lo3SPL2B03x141CFFFFS2sp2lo3SPLFFFFS2ra2sp2lo3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s5S2ra2sp2lo3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s5S2sp3BEG1n2lo3LO03SPL2B0S2sp3BEG1n2lo3LO03SPL2B0S2ra2sp2lo3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s5S2sp3BEG1n2lo3LO03SPL2B0S2ra2sp2lo3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s5S2sp3BEG1n2lo3LO03SPL2B0S2ra2sp2lo3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s5S2sp3BEG1n2lo3LO03SPL2B0S2ra2sp2lo3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s5S2sp3BEG1n2lo3LO03SPL2B0S2sp3BEG1n2lo3LO03SPL2B0S2ra2sp2lo3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s5S2ra2sp2lo3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s5S2sp3BEG1n2lo3LO03SPL2B0S3BEG1nFFFS2AL3BEG1n1N4HIGH4IMG'S3BEG1nS2AL3BEG1n4IMG'FS2sp2HBS2sp2HBS2sp2loS2sp3BEG1n2loS2sp3BEG1n2loS3BEG1nS3BEG1nS3BEG1n1N2NZS2AL3BEG1n4IMG'S2sp3BEG1n2loS2sp3BEG1n2loS2sp2loS2sp2loS3BEG1n1N2NZS3BEG1n1N2NZS2AL3BEG1n1N4HIGH4IMG'S2AL3BEG1n4IMG'FFS2sp3BEG1n2lo3SPLS2sp2lo3SPLS2sp2lo3SPLS2sp3BEG1n2lo3SPLS3BEG1nFS2ra2sp2lo2HB5Ha_st5Hl_stS2sp2s02lo2HB5Ha_st5Hl_st2s12s22s32s42s5S3BEG1n1N2B02ab2ae3Eab3Eae2M12M22D22qb3Hqb2qe3HqeS3BEG1nS2sp2lo3SPLS2sp2lo3SPLS2sp3BEG1n2lo3SPLS2sp3BEG1n2lo3SPLFS2sp3BEG1n2lo3LO03SPL3SPR2B0S3BEG1nS2AL3BEG1n1N4HIGH4IMG'S2sp3BEG1n2loS2sp3BEG1n2loS2sp2loS2sp2loS2sp3BEG1n2loS3BEG1nS3BEG1nS3BEG1nS2sp3BEG1n2lo3SPLS2sp2lo3SPLS2sp2lo3SPLS2sp3BEG1n2lo3SPLS3BEG1nFFS2sp2lo3SPLS2sp2lo3SPLS2sp3BEG1n2lo3SPLS2sp3BEG1n2lo3SPLS3BEG1n2B0S2sp3BEG1n2lo3SPLS2sp3BEG1n2lo3SPLS2sp2lo3SPLS2sp2lo3SPLS2sp3BEG1n2lo3SPLS2sp3BEG1n2loS2sp2loS2sp2loS2sp3BEG1n2loS2AL3BEG1n4IMG'FS3BEG1nS3BEG1nFS2AL3BEG1n4IMG'S2AL3BEG1n4IMG'S2sp3BEG1n2loS2sp2loS2sp2loS2sp3BEG1n2loS2AL3BEG1n1N4HIGH4IMG'FS2AL3BEG1n1N4HIGH4IMG'S2AL3ASB3BEG1n2B02ae3Eae2M22D22qe3HqeFS2sp3SPR2HB5Ha_stS2sp3SPR2HB5Ha_stS2sp3BEG1n2loS2sp2loS2sp2loS2sp3BEG1n2loS3BEG1nS3BEG1nS3BEG1n1N2NZS2AL3BEG1n5ALWF'S2AL3BEG1n5ALWF'S3BEG1nS3BEG1nS2AL3BEG1n4IMG'S2sp3BEG1n2loS2sp3BEG1n2loS2sp2loS2sp2loFS2AL3BEG1n4IMG'S2AL3BEG1n1N4HIGH4IMG'S2AL3BEG1n4IMG'FS2AL3ASB3BEG1n2B02ae3Eae2M22D22qe3HqeS2sp2lo3SPLS2sp2lo3SPLS2sp3BEG1n2lo3SPLS2sp3BEG1n2lo3SPLS2AL3BEG1n4IMG'2B0FFS2ra2sp2lo3SPL2HB5Ha_st5Hl_stS2sp2s02lo3SPL2HB5Ha_st5Hl_st2s12s22s32s42s5S2AL3BEG1n4IMG'2B0S2AL3BEG1n4IMG'2B0S2ra2sp2lo3SPL2HB5Ha_st5Hl_stS2sp2s02lo3SPL2HB5Ha_st5Hl_st2s12s22s32s42s5S3BEG1nS2sp3BEG1n2lo3SPLS2sp3BEG1n2lo3SPLS2sp2lo3SPLS3BEG1n". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK ASB"] Theorem rip_spec : ltac2:(CDefT.buildp (gd_tbl_A_rip ()) "Pra,(=.&40.)Psp,(=.&40.)Pgp,(=.&40.)Ptp,(=.&40.)Pt0,(=.&40.)Pt1,(=.&40.)Pt2,(=.&40.)Ps0,(=.&40.)Ps1,(=.&40.)Pa0,(=.&40.)Pa1,(=.&40.)Pa2,(=.&40.)Pa3,(=.&40.)Pa4,(=.&40.)Pa5,(=.&40.)Pa6,(=.&40.)Pa7,(=.&40.)Ps2,(=.&40.)Ps3,(=.&40.)Ps4,(=.&40.)Ps5,(=.&40.)Ps6,(=.&40.)Ps7,(=.&40.)Ps8,(=.&40.)Ps9,(=.&40.)Ps10,(=.&40.)Ps11,(=.&40.)Pt3,(=.&40.)Pt4,(=.&40.)Pt5,(=.&40.)Pt6,(=.&40.)PF,(1>.&5.(=.&40.))Pfc,(=.&20.)Pm,P,(=.&40.)(1?.(=.&8.))PBEG,$1.Pn,$1.Plo,$1.P,(33.$1=.VAL,VCS,R4.R3.R2.)P,(3.(4.=R3.)(5.R3.(7.+2.+28.)))P,(34.R5.(8.(8.R5.R4.)+7.))P,(20.R7.)P,(2>.$1=.R8.R5.(24.&40.R28.))P,(5.+10007???7???.R6.)P,(4.R7.(27.(24.&40.R2:.)+50.))P,(30.VCS,R8.(27.(24.&40.R2;.)R8.))P,(21.$1=.R<.)P,(16.(=.&40.)R25.(?.&40.R<.))P,(16.(=.&40.)R25.(?.&40.R<.))(25.$1=.VAL,VCS,(35.R30.R2?.R2>.R2=.R29.R28.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R11.R10.R<.R?.)(17.(18.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)R11.(?.&40.+6:>>4.)R10.(1;.(=.&40.))R?.(1<.$1=.)))")
(* [comment removed for export] *).
  Proof.
    intros until lo. intros OBJ N AR RC ST LO0 SPL SCS MI -> ->. al_facts. unfold app_range in AR.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof RC as RC'. destruct RC as [RC1 RC2 RC3 RC4 RC5 RC6 RC7 RC8].
    assert (B0 : 0 < BEG /\ BEG + n + 7 <= HME) by lia.
    carve_frame 64%nat ST.
    (* [comment removed for export] *)
    do 9 zstep.
    destruct (Z.eq_dec n 0) as [-> | NZ].
    { if_trueU. (* [comment removed for export] *)
      do 11 zstep. release_frame FR ST (bv_unsigned sp). finish. }
    if_falseU.
    set (ab := BEG + 7 - (BEG + 7) mod 8). set (ae := BEG + n - (BEG + n) mod 8).
    assert (Eab : ab = BEG + 7 - (BEG + 7) mod 8) by reflexivity. assert (Eae : ae = BEG + n - (BEG + n) mod 8) by reflexivity.
    clearbody ab ae.
    pose proof (Z.mod_pos_bound (BEG + 7) 8 ltac:(lia)) as M1. pose proof (Z.mod_pos_bound (BEG + n) 8 ltac:(lia)) as M2.
    pose proof (Z.div_mod (BEG + 7) 8 ltac:(lia)) as D1. pose proof (Z.div_mod (BEG + n) 8 ltac:(lia)) as D2.
    pose proof (Z.div_mod BEG 8 ltac:(lia)) as D0. pose proof (Z.mod_pos_bound BEG 8 ltac:(lia)) as M0.
    assert (Hqb : exists qb, ab = 8 * qb) by (exists ((BEG + 7) / 8); lia). destruct Hqb as [qb Hqb].
    assert (Hqe : exists qe, ae = 8 * qe) by (exists ((BEG + n) / 8); lia). destruct Hqe as [qe Hqe].
    (* [comment removed for export] *)
    assert (T3 : forall (r1 t0' a1' a2' a3' a4' a5' a6' a7' x18 x20 : word),
      evtA asegs AL CS (rip_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
        (MS (mkR r1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0' t1 t2 (Z_to_bv 64 BEG) (Z_to_bv 64 n)
                 (Z_to_bv 64 (SB + qe)) a1' a2' a3' a4' a5' a6' a7'
                 x18 (Z_to_bv 64 (SB + qb)) x20 (Z_to_bv 64 0x1099f8) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x6b048) fc None m0 (seg_rom asegs))).
    { intros r1 t0' a1' a2' a3' a4' a5' a6' a7' x18 x20.
      zstep.
      destruct (Z_lt_le_dec qb qe) as [LT|GE].
      - if_falseU. zstep. zstep. zstep.
        callxA_sp (bv_unsigned sp + -64)
               (eapply (miz_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0 (SB + qb) (SB + qe) lo);
                rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by lia;
                [ intros x Hx; eapply (aobj_shadow_zero_range m0 BEG n ab ae); try eassumption; try lia;
                  rewrite Hqb, Hqe, !(Z.mul_comm 8), !Z.div_mul by lia; lia
                | intros x Hx; right; left; exists (8 * (x - SB)); split;
                    [ eapply (aobj_crange _ _ _ _ _ _ ltac:(eassumption)); lia | unfold shadow_of; rewrite ASB; rewrite Z.mul_comm, Z.div_mul by lia; lia ]
                | lia | lia | lia | assumption | reflexivity | f_equal; rewrite !Z.mod_small by lia; lia | lia
                | eassumption | lia | lia | eapply crange_sub; [exact SCS | lia | lia] | lia | reflexivity ]).
        (* [comment removed for export] *)
        do 12 zstep. lazymatch goal with H : stk _ _ lo _ |- _ => release_frame FR H (bv_unsigned sp) end. finish.
      - if_trueU. do 11 zstep. release_frame FR ST (bv_unsigned sp). finish. }
    (* [comment removed for export] *)
    lazymatch goal with H : aobj _ _ _ m0 BEG n |- _ => rename H into OBJ0 end.
    (* [comment removed for export] *)
    assert (T2 : forall (r1 t0' a2' a3' a4' a5' a6' a7' x20 : word),
      evtA asegs AL CS (rip_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
        (MS (mkR r1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0' t1 t2 (Z_to_bv 64 BEG) (Z_to_bv 64 n)
                 (Z_to_bv 64 (SB + qe)) (Z_to_bv 64 SB) a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 (BEG + n)) (Z_to_bv 64 (SB + qb)) x20 (Z_to_bv 64 0x1099f8) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x6aff4) fc None m0 (seg_rom asegs))).
    { intros r1 t0' a2' a3' a4' a5' a6' a7' x20.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      shadow_byte OBJ0 (BEG + n + -1) 1 as k RD HK.
      (* [comment removed for export] *)
      zstep. zstep.
      if_cases Kz; zify_cond Kz.
      - apply T3.
      - (* [comment removed for export] *) zstep. zstep.
        lazymatch goal with
        | |- _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) =>
            replace cnd with true by (symmetry; eapply (shadow_slow_takenN (BEG + n + -1) 1 k _ HK Kz); qlia); cbv iota
        end.
        apply T3. }
    (* [comment removed for export] *)
    assert (T1 : forall (r1 t0' a1' a2' a3' a4' a5' a6' a7' x20 : word),
      evtA asegs AL CS (rip_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
        (MS (mkR r1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0' t1 t2 (Z_to_bv 64 BEG) (Z_to_bv 64 n)
                 (Z_to_bv 64 (SB + qe)) a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 (BEG + n)) (Z_to_bv 64 (SB + qb)) x20 (Z_to_bv 64 0x1099f8) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x6afd8) fc None m0 (seg_rom asegs))).
    { intros r1 t0' a1' a2' a3' a4' a5' a6' a7' x20.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      shadow_byte OBJ0 BEG 1 as k RD HK.
      (* [comment removed for export] *)
      zstep. zstep.
      if_cases Kz; zify_cond Kz.
      - apply T2.
      - (* [comment removed for export] *) zstep. zstep.
        lazymatch goal with
        | |- _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) =>
            replace cnd with false by (symmetry; apply (proj2 (Bool.negb_false_iff _)); eapply (shadow_slow_takenN BEG 1 k _ HK Kz); qlia); cbv iota
        end.
        apply T2. }
    assert (RCm0 : rip_consts m0) by (split; assumption).
    (* [comment removed for export] *)
    assert (T0 : forall (r1 t0' a0' a1' a2' a3' a4' a5' a6' a7' x19 x20 : word),
      evtA asegs AL CS (rip_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
        (MS (mkR r1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0' t1 t2 (Z_to_bv 64 BEG) (Z_to_bv 64 n)
                 a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 (BEG + n)) x19 x20 (Z_to_bv 64 0x1099f8) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x6afb8) fc None m0 (seg_rom asegs))).
    { intros r1 t0' a0' a1' a2' a3' a4' a5' a6' a7' x19 x20.
      (* [comment removed for export] *)
      zstep. if_falseU. zstep. zstep. zstep. rewrite !land_m8 by lia. rewrite <- Eab, <- Eae. zstep.
      eapply evtA_cut; [eapply (m2s_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0 ab);
                         [exact RCm0 | assumption | unfold app_mem; lia | reflexivity | reflexivity]
                       | cbn beta; intros ms' PO; unfold m2s_post in PO; destruct_exs PO; subst ms'].
      replace (ret_pc (Z_to_bv 64 0x6afcc)) with (Z_to_bv 64 0x6afcc) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      eapply evtA_cut; [eapply (m2s_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0 ae);
                         [exact RCm0 | assumption | unfold app_mem; lia | reflexivity | reflexivity]
                       | cbn beta; intros ms' PO; unfold m2s_post in PO; destruct_exs PO; subst ms'].
      replace (ret_pc (Z_to_bv 64 0x6afd8)) with (Z_to_bv 64 0x6afd8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      rewrite Hqb, Hqe, !(Z.mul_comm 8), !Z.div_mul by lia.
      apply T1. }
    (* [comment removed for export] *)
    do 10 zstep.
    change (Z.land ((Z.b2z (2147450880 <? 2147450879) + -1) mod 18446744073709551616) 2147450879) with 2147450879.
    destruct AR as [LOW | HIGH].
    - (* [comment removed for export] *)
      if_trueU. (* [comment removed for export] *) zstep. zstep. replace (n + BEG) with (BEG + n) by lia. if_trueU.
      apply T0.
    - if_falseU.
      (* [comment removed for export] *)
      do 8 zstep. rewrite Z_to_bv_m1. if_trueU.
      (* [comment removed for export] *)
      do 5 zstep. zstep. if_falseU. zstep. if_falseU.
      (* [comment removed for export] *)
      zstep. zstep. replace (n + BEG) with (BEG + n) by lia. if_falseU.
      (* [comment removed for export] *)
      do 8 zstep. rewrite Z_to_bv_m1. if_trueU.
      (* [comment removed for export] *)
      do 5 zstep. zstep. if_falseU. zstep. if_falseU.
      apply T0.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.