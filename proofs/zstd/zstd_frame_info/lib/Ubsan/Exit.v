(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import StrFun STRW_tac Startup_kit Amo_tac.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Monad Stdio Driver.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg F_syscalls Startup_A StdioFiles F_atexit.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

Notation rsegs := UImg.usegs.

(* [comment removed for export] *)
Notation PEXIT_ENTRY := 0x14174%Z (only parsing).
Notation PFUNCS_ON_EXIT := 0x13f90%Z (only parsing).
Notation PLIBC_EXIT_FINI := 0x14128%Z (only parsing).
Notation PSTDIO_EXIT := 0x16434%Z (only parsing).
Notation P_EXIT := 0x141e8%Z (only parsing).
Notation PEXIT_LOCK := 0x4e290%Z (only parsing).
Notation PFINALIZED := 0x1df28%Z (only parsing).
Notation PDSO_HANDLE := 0x1dcd0%Z (only parsing).
Notation PGOT_CXA := 0x1cc68%Z (only parsing).       (* [comment removed for export] *)
Notation PGOT_FINI := 0x1ccc0%Z (only parsing).      (* [comment removed for export] *)
Notation PFINI_ARRAY := 0x1cc20%Z (only parsing).    (* [comment removed for export] *)
Notation RTD := 0x2df68%Z (only parsing).            (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma p_Exit_spec : forall (code : Z) (Q : Empty_set -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv rsegs m ->
  a0 = Z_to_bv 64 code ->
  impl rsegs (at_node rsegs) (enode (NExit code) dec_exit) (epost Q)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 P_EXIT) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros MI ->.
  pose proof (wmono_refl rsegs m) as WM.
  apply impl_enode. do 2 lstep. step_ecall.
  split; [ at_node_red; split; [right; reflexivity | reflexivity] | intros rsp a H; cbn in H; discriminate H].
Qed.

(* [comment removed for export] *)
Lemma p_Exit_specM : forall {St : Type} (s : St) (code : Z) (Q : Empty_set -> St -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv rsegs m ->
  a0 = Z_to_bv 64 code ->
  implM rsegs (msys (NExit code) dec_exit) s Q
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 P_EXIT) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros MI ->.
  pose proof (wmono_refl rsegs m) as WM.
  apply implM_sys. do 2 lstep. step_ecall.
  split; [ at_node_red; split; [right; reflexivity | reflexivity] | intros rsp a H; cbn in H; discriminate H].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pfuncs_on_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x4e070, 0x4e071); (0x4e078, 0x4e07c); (0x4e080, 0x4e088)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp).

Lemma pfuncs_on_exit_spec : forall (reg : bool) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (cdt thr sec : byte) (tm1 : word),
  stk rsegs m lo (bv_unsigned sp) ->
  atx_state reg m ->
  rw_cells rsegs m 0x4e2b8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->    (* [comment removed for export] *)
  mem_inv rsegs m ->
  (lo <= bv_unsigned sp - 48)%Z -> (0x4f000 <= lo)%Z ->
  evt rsegs (pfuncs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PFUNCS_ON_EXIT) fc None m (seg_rom rsegs)).
Proof.
  intros until tm1. intros ST ((X1 & X2 & X3 & X4 & X5 & X6 & X7) & CB) LCH MI LO LOLO.
  unfold PATX, PATX_CALLFN, PEXIT_GUARD, PAEF_INCB in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x4e070, 0x4e071); (0x4e078, 0x4e07c); (0x4e080, 0x4e088)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  Local Ltac2 Set LiaHints.tbl := fun () => "02>0>11903774446.6812205715893.6612205715893.6812299880250.6912299880250.731800609155.66 1800609155.67 18634373998.6719693786893.6822389541692.6524494849774.6624638473347.6724638473347.6925105202362.6625105202362.6825206890358.6525771339118.6526235044154.6926235044154.7327865992944.6827906909603.5827908601838.6528176222394.6628176222394.6828290880502.6428417259964.6730180773870.6530873494640.6930873494640.7331378308326.5832678515898.6632678515898.6832795189110.6733680001082.6834004991342.6734430152252.6835310472686.6736066158.67   36370459630.6737048456378.6637048456378.6837351378874.6837558276410.6937558276410.7338889585390.6839024948917.6839661655098.6939661655098.7339693769198.6540069102958.6740457739452.6641161757422.6841710833594.6841930314042.6941930314042.7342744733806.6643059266230.5643185646906.6943185646906.734347007418.68 43913974254.6743988483203.6543988483203.6744500894574.6745221239098.6745848756903.6546468661564.6747079788730.6647079788730.6847472103150.6848527617037.6648527617037.6849147187950.6849649769127.6849676673978.6849978085870.675039673326.65 50837928942.6551711223320.5752105090727.6752136437230.6752320852277.6952320852277.7352567164907.6552567164907.6652567164907.6752567164907.6852567164907.6952567164907.7353850141114.6854243526019.6654243526019.6854569212142.6855320280250.6655320280250.6856023003502.67563227834.66  56635794422.6456912526318.6557597764590.6757745675194.6757774688366.6858691506160.6658691506160.6858732652910.6758871667702.6659377599629.6959377599629.7359382628974.6659426343926.6459428705082.6959428705082.7360128159214.6760258122606.6760592618094.6660858483367.6761353657710.6561559103930.6861889066042.6961889066042.736269928558.66 63118127290.6663118127290.6863305555623.6663666760686.6764997134979.6764997134979.6864997134979.6966588768442.6666588768442.6867003974766.6667663283182.6768578752238.667227556282.68 7651291246.68 8384152046.65 8583720762.65 8722841838.68 9256566202.68 9595551854.66 9844715886.67 992066670.66  00000900B00K00L00M00N00O00X00Y00]00f00g00h00i00j00k01401501601701;01D01E01F01G01K01T01U01V01W01X01Y01Z01_01h01l02502>02G02H02I02J02K02L02U02^02_02`02i03203603?03@03A03B03K03O03P03Q03R03[03\03]03f03k03l04004104204;04<04=04F04G04H04Q04Z04c04d04e04n05705@05A05B05C05D05E05F05G05H05I05R05S05T05]05b05c05l06506:06C06D06E06N06O06P06Q06Z06[06\06]06f06o07807907B07C07D07E07N07O07P07Q07Z07[07\07]07^07_07h08108:08;08D08M08R08[08\08e08n097S2LO4LOLOS2LO4LOLOS2LO4LOLOSSSSS2LO4LOLOSS2HBS2LO4LOLOSSSSSS2LO4LOLOSSSS2LOS2LO4LOLOSSSS2HBS2LO4LOLOSSSSSSS3RSPS2LO4LOLOS2HBS2LO4LOLOS2LO4LOLOS2LO4LOLOSSSSSS2LO4LOLOS2LO4LOLOSSS2LO4LOLOS2LO4LOLOS2HBS2LO4LOLOSSSS2LO4LOLOS2LOSSSS2LO4LOLOSSS2LO4LOLOS3RSPSS2HBSSS2LO4LOLOSSS2LO4LOLOSSS2LO4LOLOS2LO4LOLOS2LO4LOLOSSS2LO4LOLOS2LO4LOLOS2LO4LOLOSSSSSSSSSS2LO4LOLOSSS2LO4LOLOS3RSPSS2LO4LOLOS2LO4LOLOS3RSPS2LO4LOLOSSS2LO4LOLOSSSS2LO4LOLOSSSS2LO4LOLOS2LO4LOLOS2LO4LOLOSS2LO4LOLOSSSS2LO4LOLOSSSS2LO4LOLOSSSSSS2LO4LOLOS2LO4LOLOS2LO4LOLOSS2LO4LOLOS2LO4LOLOS3RSPS2LO4LOLOSS2LO4LOLOS2LO4LOLOS2LO4LOLO".
carve_frame 48%nat ST.
  (* [comment removed for export] *)
  steps_to 0x1b848%Z.
  lstep. lstep. lstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. lstep.
  (* [comment removed for export] *)
  lstep.
  destruct reg; cbn [negb andb orb] in *.
  - (* [comment removed for export] *)
    lstep. if_false.
    (* [comment removed for export] *)
    lstep. try replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (vm_compute; reflexivity).
    lstep. lstep. try change (bv_swrap 32 (1 + -1))%Z with 0%Z. lstep. lstep. if_false.
    (* [comment removed for export] *)
    steps_to 0x1bad0%Z.
    lstep. try replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) by (vm_compute; reflexivity). lstep. if_false. lstep.
    (* [comment removed for export] *)
    steps_to 0x12c14%Z.
    lstep. lstep. lstep. if_false. lstep.
    (* [comment removed for export] *)
    steps_to 0x1b848%Z.
    lstep. lstep. lstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. lstep.
    (* [comment removed for export] *)
    lstep. try replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) by (vm_compute; reflexivity).
    lstep. try change (bv_swrap 32 (0 + -1))%Z with (-1)%Z. lstep. lstep. if_false.
    (* [comment removed for export] *)
    steps_to 0x13fdc%Z. lstep. if_true.
    (* [comment removed for export] *)
    steps_to 0x14050%Z.
    release_frame FR ST (bv_unsigned sp). astep. astep.
    lstep. try replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) by (vm_compute; reflexivity). lstep. if_false. lstep.
    unfold pfuncs_on_exit_post, PATX. sys_finish.
  - (* [comment removed for export] *)
    lstep. if_true.
    steps_to 0x14050%Z.
    release_frame FR ST (bv_unsigned sp). astep. astep.
    lstep. try replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) by (vm_compute; reflexivity). lstep. if_false. lstep.
    unfold pfuncs_on_exit_post, PATX. sys_finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition plibc_exit_fini_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (PFINALIZED, PFINALIZED + 1)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' PFINALIZED [C1 (Z_to_bv 8 1)].

Lemma plibc_exit_fini_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m PGOT_FINI [C8 (Z_to_bv 64 0x1cc28); C8 (Z_to_bv 64 PFINI_ARRAY)] ->   (* [comment removed for export] *)
  rw_cells rsegs m PFINI_ARRAY [C8 (Z_to_bv 64 0x1275c)] ->                              (* [comment removed for export] *)
  rw_cells rsegs m PFINALIZED [C1 (Z_to_bv 8 0)] ->                                      (* [comment removed for export] *)
  rw_cells rsegs m PGOT_CXA [C8 (Z_to_bv 64 0x14058); C8 z64] ->                          (* [comment removed for export] *)
  rw_cells rsegs m PDSO_HANDLE [C8 (Z_to_bv 64 PDSO_HANDLE)] ->                          (* [comment removed for export] *)
  mem_inv rsegs m ->
  (lo <= bv_unsigned sp - 48)%Z -> (0x4f000 <= lo)%Z ->
  evt rsegs (plibc_exit_fini_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PLIBC_EXIT_FINI) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST GF FA FIN GCX DSO MI LO LOLO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x1df28, 0x1df28 + 1)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* [comment removed for export] *)
  Local Ltac2 Set LiaHints.tbl := fun () => "0170>1309658265.59 16622434386.6016781328285.6017221588796.5617423251694.5618625126638.5619006120615.5919622476014.5619964125230.5119987060046.5220979536691.6022236668526.5823230285244.5824638473347.5925071629079.5625071629079.5825071629079.5925071629079.6025071629079.6525373284405.6525566553219.5925566553219.6026826268730.6526924678012.5127679091076.5027905104286.5229514832494.5829870281326.5830408359482.6530521385966.5931155415208.5031521058898.6032377744366.5932716547054.5933680001082.5634290115814.4938446806799.6038806986883.5638806986883.5839939243268.5141564619544.5042831019478.6043059266230.4743836933870.5645221239098.5946356275438.5646468661564.5947092256565.6547586416750.5847944968589.6550356509686.5851139856210.605180980284.59 53113023478.5753443621946.6553605654098.6054618151079.5854817786350.5955104759171.5855104759171.59563227834.58  56981146544.6057969830970.6558016127598.5860858483367.596166287527.56 62987630418.6063404311920.6565098116726.5867208578631.5267324480494.5900000100:00;00?00H00Q00R00[00\00]00^00g00k00l00m00n00o01001101:01;01<01=01>01B01F01O01X01Y01b01c01l02502>02C02D02E02F02G02K02L02Q02U02^02c02l03003903B03C03D03M03Q03R03S03\03]03f03g03h03m04104204;04<04=04F04G04H04I04RSS2LO4LOLOSS2HBS2LO4LOLOS2LO4LOLOSS2LO4LOLOFFSS2LO4LOLOS2HBSSSSSSS2LO4LOLOSSSSS2LOS2LOS2LO4LOLOS2LO4LOLOSS2LO4LOLOFS2LO4LOLOS2LO4LOLOS2LO4LOLOS3RSPSSSSS2LOSS3RSPS2LOS2LO4LOLOS3RSPS2LO4LOLOS2HBS2LO4LOLOS2LO4LOLOSSS2LO4LOLOS2HBSSS2LO4LOLOSS2LO4LOLOSSS3RSPS2HBSS2LO4LOLOSSS2LO4LOLOSSSS2LO4LOLO".
carve_frame 32%nat ST. steps_to 0x1275c%Z.
  (* [comment removed for export] *)
  carve_frame 16%nat ST. steps_to 0x127e4%Z. release_frame FR0 ST (bv_unsigned sp + -32)%Z. astep. astep.
  (* [comment removed for export] *)
  steps_to 0x1416c%Z. release_frame FR ST (bv_unsigned sp). astep. astep. astep.
  unfold plibc_exit_fini_post. sys_finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pexit_prefix_post (sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo code t : Z) (td0 td1 td2 td3 ra : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x141e0) (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 RTP) t0 t1 t2 (Z_to_bv 64 code) s1
                 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 PSTDIO_EXIT) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (PEXIT_LOCK, PEXIT_LOCK + 4); (PFINALIZED, PFINALIZED + 1);
              (0x4e070, 0x4e071); (0x4e078, 0x4e07c); (0x4e080, 0x4e088)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp + -16)
    /\ rw_cells rsegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra]
    /\ rw_cells rsegs m' RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)]
    /\ rw_cells rsegs m' PEXIT_LOCK [C4 (Z_to_bv 64 t)]
    /\ rw_cells rsegs m' PFINALIZED [C1 (Z_to_bv 8 1)].

Lemma pexit_prefix_spec : forall (reg : bool) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (code t : Z) (td0 td1 td2 td3 : word)
    (cdt thr sec : byte) (tm1 : word),
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->      (* [comment removed for export] *)
  rw_cells rsegs m PEXIT_LOCK [C4 z64] ->                                           (* [comment removed for export] *)
  rw_cells rsegs m PGOT_FINI [C8 (Z_to_bv 64 0x1cc28); C8 (Z_to_bv 64 PFINI_ARRAY)] ->   (* [comment removed for export] *)
  rw_cells rsegs m PFINI_ARRAY [C8 (Z_to_bv 64 0x1275c)] ->                        (* [comment removed for export] *)
  rw_cells rsegs m PFINALIZED [C1 (Z_to_bv 8 0)] ->                                (* [comment removed for export] *)
  rw_cells rsegs m PGOT_CXA [C8 (Z_to_bv 64 0x14058); C8 z64] ->                    (* [comment removed for export] *)
  rw_cells rsegs m PDSO_HANDLE [C8 (Z_to_bv 64 PDSO_HANDLE)] ->                    (* [comment removed for export] *)
  rw_cells rsegs m 0x4e2b8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->    (* [comment removed for export] *)
  atx_state reg m ->                                                                (* [comment removed for export] *)
  mem_inv rsegs m ->
  tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
  (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 64)%Z -> (0x4f000 <= lo)%Z ->
  evt rsegs (pexit_prefix_post sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code t td0 td1 td2 td3 ra m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PEXIT_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros until tm1. intros ST TDa EXL GF FA FIN GCX DSO LCH AX MI -> -> Ht LO LOLO.
  (* [comment removed for export] *)
  destruct AX as [(X1 & X2 & X3 & X4 & X5 & X6 & X7) CB]. unfold PAEF_INCB in CB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (0x4e290, 0x4e290 + 4); (0x1df28, 0x1df28 + 1);
                          (0x4e070, 0x4e071); (0x4e078, 0x4e07c); (0x4e080, 0x4e088)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  Local Ltac2 Set LiaHints.tbl := fun () => "01T0?11656353059.10211658450183.87 11970073274.72 12430247196.1021343986644.87  15417454543.87 15539463119.87 16622434386.80 18040096338.80 18634373998.77 20433961190.70 20948333063.10322428323719.10223160441530.72 25073974703.10325387547474.80 25531754170.72 25632264527.87 27730847314.80 28696517455.87 30373476943.87 30521385966.77 31521058898.80 31781556718.77 32377744366.77 32600174396.77 32625853114.72 32716547054.77 33534404109.72 34031823111.10334194231792.72 35234503354.72 3525607222.68  3525607222.84  35310472686.77 35450521274.72 35624951350.71 36066158.77    36370459630.77 36634911984.71 36641385327.72 37429491794.80 39517401529.80 39521875765.64 39949608786.80 40201484047.80 40310101714.80 42148986991.64 42152937187.80 42831019478.80 43059266230.68 43104399792.80 43283641650.98 43913974254.77 45221239098.77 45241786759.10245341821626.72 45843348154.72 46134254574.77 4744560338.80  47935039314.80 48744835207.10349978085870.77 51139856210.80 52136437230.77 52567164907.72 52567164907.77 52567164907.80 52579502455.87 53605654098.80 54164510851.77 54605059791.87 54817786350.77 56204444054.83 57622410744.10358325261447.10358479499143.10259314923118.72 60083716794.72 60128159214.77 6049873717.103 60614068922.72 62251784274.80 62583080755.80 62987630418.80 63142967631.87 63198633479.10363296330426.72 63299176018.80 6385300154.72  65475822005.72 661312186.72   66399320762.72 67081926311.77 67324480494.77 67663283182.77 67759509071.87 7021785682.80  7457097402.72  8800126135.88  00000100200300400500B00O00X00a00j00k00l01901:01G01P01Q01^01g02402A02J02S02\02e02i02j03303403A03B03C03R03a03j03k03o04804A04E04I04R04V04Z04c04d04m05305905>05B05F05G05P05U05b05c05d05m06606?06L06U06^06g06h06i06j07707@07A07N07W07X07g08408A08G08H08Q08^08_08h08i09209?09L09M09V09W09`09a09b09c09l0:50:B0:K0:L0:[FFSFFS2LO4LOLO3HspS2LO4LOLO3HspS2LO4LOLOS2LO4LOLOS2LO4LOLOSFS2LO4LOLO3HspSS2LO4LOLO3HspS2LO4LOLOSS2LO4LOLO3HspS2LO4LOLOS2LO4LOLO3HspS2LO4LOLO3HspS2LO4LOLOS2LO4LOLOS2LO4LOLOS2LO4LOLOS2HBSS2LO4LOLOSS2LO4LOLO3HspSSS2LO4LOLO3RSP1HS2LO4LOLO3RSP1HS2LO4LOLOSS2HtS2LO4LOLOS2LO4LOLOS2HtS2HtS2LO4LOLOS2LOS2LOS2LO4LOLOSS2LO4LOLOS4LOLOS4LOLOS3RSPS2LOS2HBSS2LO4LOLOS3RSPS2LO4LOLO3HspSSS2LO4LOLOS2LO4LOLOS2LO4LOLOS2LO4LOLO3HspS2LO4LOLOS2LO4LOLOS2LO4LOLOSSSS2LO4LOLO3HspS2LO4LOLOSS2LO4LOLO3HspS2LO4LOLOSS2LO4LOLO3Hsp1HS2LO4LOLO3HspS2LO4LOLO3HspS2Ht1KSS2LO4LOLOS2LO4LOLO3HspSS2LO4LOLOSS2LO4LOLOS2LO4LOLO3HspS2LO4LOLO3HspSS2LO4LOLOSS2LO4LOLOSSSS2LO4LOLOS2LO4LOLOS2LO4LOLO3HspS2LO4LOLOSS2LO4LOLO3Hsp1H".
carve_frame 16%nat ST.
  do 6 lstep.
  replace (sx32 (Z_to_bv 64 t)) with (Z_to_bv 64 t)
    by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_small; lia).
  lstep. lstep.
  (* [comment removed for export] *)
  amo_step. replace (sx32 z64) with z64 by (vm_compute; reflexivity).
  lstep. if_false. amo_step. lstep. if_false.
  lstep. change (bv_swrap 32 (0 + 0)) with 0%Z.
  lstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K. lstep. if_true.
  (* [comment removed for export] *)
  steps_to 0x13f90%Z.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (AX : atx_state reg mx) by (exact (conj (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 X7)))))) CB)) end.
  clear X1 X2 X3 X4 X5 X6 X7 CB.
  call_sp (pfuncs_on_exit_spec reg);
    [ exact ST | exact AX | exact LCH | exact MI | lia | lia | ].
  (* [comment removed for export] *)
  astep.
  call_sp plibc_exit_fini_spec;
    [ hyp_by_addr | hyp_by_addr | hyp_by_addr | hyp_by_addr | hyp_by_addr | hyp_by_addr | hyp_by_addr | lia | lia | ].
  (* [comment removed for export] *)
  astep.
  unfold pexit_prefix_post, PATX. sys_finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Section ExitProof.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  (* [comment removed for export] *)
  Hypothesis stdio_exit_spec : stdio_exit_spec_stmt get_so set_so.

  #[using="stdio_exit_spec"] Lemma exit_spec : forall (reg : bool) (s : St) (Q : Empty_set -> St -> machine_state -> Prop)
      ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (code t : Z) (td0 td1 td2 td3 guard : word)
      (cdt thr sec : byte) (tm1 : word),
    stk rsegs m lo (bv_unsigned sp) ->
    rw_cells rsegs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->      (* [comment removed for export] *)
    rw_cells rsegs m PEXIT_LOCK [C4 z64] ->                                           (* [comment removed for export] *)
    rw_cells rsegs m PGOT_FINI [C8 (Z_to_bv 64 0x1cc28); C8 (Z_to_bv 64 PFINI_ARRAY)] ->   (* [comment removed for export] *)
    rw_cells rsegs m PFINI_ARRAY [C8 (Z_to_bv 64 0x1275c)] ->                        (* [comment removed for export] *)
    rw_cells rsegs m PFINALIZED [C1 (Z_to_bv 8 0)] ->                                (* [comment removed for export] *)
    rw_cells rsegs m PGOT_CXA [C8 (Z_to_bv 64 0x14058); C8 z64] ->                    (* [comment removed for export] *)
    rw_cells rsegs m PDSO_HANDLE [C8 (Z_to_bv 64 PDSO_HANDLE)] ->                    (* [comment removed for export] *)
    rw_cells rsegs m 0x4e2b8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->    (* [comment removed for export] *)
    atx_state reg m ->                                                                (* [comment removed for export] *)
    rw_cells rsegs m 0x4e6e8 [C8 z64] -> rw_cells rsegs m 0x4e6d8 [C8 z64] ->         (* [comment removed for export] *)
    rw_cells rsegs m 0x1ded0 [C8 (Z_to_bv 64 RSTDOUT)] -> rw_cells rsegs m 0x1dde0 [C8 (Z_to_bv 64 RSTDERR)] ->  (* [comment removed for export] *)
    stdout_file m (get_so s) -> stderr_file m ->
    rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells rsegs m ssp_guard [C8 guard] ->
    mem_inv rsegs m ->
    tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
    (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 176)%Z -> (0x4f000 <= lo)%Z ->
    (bv_unsigned sp < 2^47)%Z ->                      (* [comment removed for export] *)
    implM rsegs (Driver.exit_model (io_S get_so set_so) code) s Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 PEXIT_ENTRY) fc None m (seg_rom rsegs)).
  Proof.
    intros until tm1. intros ST TDa EXL GF FA FIN GCX DSO LCH AX OFL SIN SOU SEU SOF SEF GG GU MI -> -> Ht LO LOLO SP47.
    unfold got_ssp, ssp_guard in GG, GU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    (* [comment removed for export] *)
    destruct SOF as (flg & mode & tail & bufb & SOF1 & SOF2 & SOF3 & SOF4 & SOF5 & SOF6).
    destruct SEF as (flg' & mode' & ee & wend' & tail' & SEF1).
    unfold file_cells in SOF1, SEF1.
    unfold Driver.exit_model.
    eapply (implM_bind rsegs _ _ s
              (fun _ _ ms' => exists sp' gp' tp' x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m',
                 ms' = MS (mkR (Z_to_bv 64 0x141e0) sp' gp' tp' x5 x6 x7 (Z_to_bv 64 code) x9 x10 x11 x12 x13 x14 x15 x16 x17
                               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                          F (Z_to_bv 64 0x141e0) fc None m' (seg_rom rsegs))).
    - (* [comment removed for export] *)
      change (io_exit (io_S get_so set_so)) with (stdout_exit_flush get_so set_so).
      unfold implM. iprefix.
call (pexit_prefix_spec reg); [exact ST | exact TDa | exact EXL | exact GF | exact FA | exact FIN | exact GCX | exact DSO | exact LCH | exact AX | exact MI
                              | reflexivity | reflexivity | lia | lia | lia | ].
      name_sp sp (-16)%Z.
      pose proof stdio_exit_spec as SE. unfold stdio_exit_spec_stmt, implM, got_ssp, ssp_guard, GLOBALS_TOP in SE.
      apply evt_done. eapply impl_epost_mono; [eapply SE|].
      all: lazymatch goal with
           | |- forall _, _ =>
               intros [[] s'] ms' PO; cbn [fst snd] in PO; unfold stdio_exit_post in PO;
               destruct_exs PO; destruct PO as (E & PO); subst ms'; cbn [fst snd];
               replace (ret_pc (Z_to_bv 64 0x141e0)) with (Z_to_bv 64 0x141e0) by (symmetry; apply ret_pc_even; [lia|reflexivity]);
               repeat eexists; cbv delta [mkR]; reflexivity
           | |- stdout_file _ _ => exists flg, mode, tail, bufb; exact (conj SOF1 (conj SOF2 (conj SOF3 (conj SOF4 (conj SOF5 SOF6)))))
           | |- stderr_file _ => exists flg', mode', ee, wend', tail'; exact SEF1
           | |- _ => unname_sp; first [ hyp_by_addr | reflexivity | lia ]
           end.
    - (* [comment removed for export] *)
      clear SOF1 SOF2 SOF3 SOF4 SOF5 SOF6 SEF1.
      intros [] s' ms' PO. destruct_exs PO. subst ms'.
      apply implM_sys. do 4 lstep. step_ecall.
      split; [ at_node_red; split; [right; reflexivity | reflexivity] | intros rsp a H; cbn in H; discriminate H].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End ExitProof.
