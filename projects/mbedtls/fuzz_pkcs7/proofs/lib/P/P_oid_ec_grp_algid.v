(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux AStep CellsX Image.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_string P_oid P_oid_x509_ext.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxSum LxSoundSum LxTac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac LxP_SumsOid.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P01b6195ebdcab0a7 0 4 0 1 1 1 18 1 22 1P0724319fac81ec44 2 23 1 1 8 3 2 1 33 1 34 1 5 0 2 24 2 32 2 35 2 36 16 1 1 8 3 1 1 32 1 35 1 4 0 2 33 2 34 2 36 16P087ac84578a4531b 2 21 0 6 0 1 3 1 25 1 29 1 33 1 34 1 0 4 0 1 2 1 33 1 34 1P0d0244b66f970434 1 1 8 2 0 1 25 1 3 10 1 26 1 27 8P0f71b70ac5877e41 0 4 0 8 9 8 25 8 26 8P111803e3a13ba17d 0 3 0 1 2 1 21 1P12d79c880de0b2aa 0 2 0 1 35 1P13e86ac0ccd1a27f 0 3 0 1 25 1 37 1P154aea195fbf65a3 0 2 0 1 23 1P15bc0065d8ec856f 2 23 1 1 8 3 2 1 33 1 34 1 5 0 2 24 2 32 2 35 2 36 16 1 1 8 3 1 1 32 1 35 1 4 0 2 33 2 34 2 36 16P16adeb1358fe32f0 0 2 0 1 24 1P1710bfc01dcf949b 0 2 0 1 24 1P1b6a66bd1d0c6926 1 1 8 2 20 1 26 1 3 0 1 25 1 27 8P1bfa48b2cf1c16c6 0 2 0 1 33 1P1c75142395c572d4 2 22 1 1 4 3 2 1 33 1 34 1 5 0 4 24 4 32 4 35 4 36 16 1 1 4 3 1 1 32 1 35 1 4 0 4 33 4 34 4 36 16P234286584e66891c 0 2 0 1 2 1P25179e19b20ad3bc 2 23 1 1 8 3 2 1 33 1 34 1 5 0 2 24 2 32 2 35 2 36 16 1 1 8 3 1 1 32 1 35 1 4 0 2 33 2 34 2 36 16P29935fc55c0ccee1 0 2 0 1 1 1P2aaf7795dfa2ff0d 0 4 0 1 5 1 36 1 37 1P2bab4771975afecb 0 2 0 1 23 1P2be6295a4b2ffdf7 0 2 0 1 1 1P2c45cf39a503018a 2 22 1 1 4 3 2 1 33 1 34 1 5 0 4 24 4 32 4 35 4 36 16 1 1 4 3 1 1 32 1 35 1 4 0 4 33 4 34 4 36 16P2e5c7fbadeb38f2e 0 2 0 1 2 1P3060779628227ff7 0 3 0 1 2 1 21 1P334a573060fe0c52 0 3 0 1 27 1 39 1P36288b6d1531eb7b 0 4 0 1 7 1 38 1 39 1P36b4d5f3d81aea1a 2 22 1 1 4 3 2 1 33 1 34 1 5 0 4 24 4 32 4 35 4 36 16 1 1 4 3 1 1 32 1 35 1 4 0 4 33 4 34 4 36 16P3831687f0171ec0e 2 21 0 6 0 1 3 1 25 1 29 1 33 1 34 1 0 4 0 1 2 1 33 1 34 1P3cfd255d6744e86d 2 21 0 6 0 1 3 1 25 1 29 1 33 1 34 1 0 4 0 1 2 1 33 1 34 1N0043fc113cbf62abN00ff2775a8e889afN01ac62a03d7a0f83N02b0abdfbc5d487dN04bfefb8a73fcdeaN04d69d07cf6958d8N05593e517bb4cbdeN0642504cbe30f71dN074301751fbdfe30N07580a6d01b6c6c3N07ea8118cf4661b3N09e8ac5f4fa42fceN0a4e23df03807355N0b4ba8e8b4a8f133N0b90df3d1998e6a8N0d73ec048b5aea09N0d8b3f9205fd566bN0ea72749ccbab19cN0f121f39be3b6b6aN0f456e9aff7084fcN0fee40cddb2c06dcN1020abae4a74f08aN104f26abcf3a8bd7N12bf512f0f119085N12c471b82ed2d4b3N14071d6392b5bceaN14d62e0c6597aae9N1520cf0eb471778eN1538a8f86bca170bN162dcdda21c9fa1eN17af03ef2533c7f1N186c36f246280da9N18b6049265705df2N193bd04feb519693N195006ea6c469e53N19e05983268d78a4N1a1557f4aacee8abN1a4252cdc50ba0afN1a9b05552547e67fN1b0c1d37e839e16cN1c28371ded66757fN1cfb36cdc342a1b0N1db3cf4b534d7bcfN1ebb5d1552586924N1fa1b63d5de6a0baN1fe795641fbb0ad6N1ff765d833ba7813N206a63ff636e2aaaN2070cbe0cc6aad6cN22be4f5cbbf07795N231fcc1a9d980a54N2409c3781afc1b80N2411f1f9629dc1f0N244378e65921233cN251c6ef57073df26N25efb794e38184b7N268f1ba08144bc4cN26bb6ded91e9f535N271ec2ebaafac3e7N27381b00fc629bb8N2742f8d4eb1f5241N27ba20db1a6f07a0N281f3d9fa683ade2N284fd512703a4d8dN2ae55f1f633c772eN2ce0ba8a741cdac7N2e7d9e4d91af4daaN2f00fc05d2a25757N2fe823d34a5de7acN31ad773b16de2d00N31f9bd3b606f944dN320bf13c32110422N3217cf3f57da3e22N32600557b55e413eN3306a69ec9f77ab4N33bcbc479aa074e1N33edd9f5e2af1ecdN3409d253c4694adbN344765aa614a6a6aN3480377e74538823N34b31f42eda7b945N3563f47a8805e090N35a3229fb8a70898N36474311cd0efe4eN36ad46a28adb089cN3720c3aede2f67ddN37f4dde21b65ad3eN381ffe28dd3ea0dbN38290681f2b02db0N38879b5ec8c41fa8N38aeef63287a0a0aN3956c906e17b7dbcN39daf0fc60ac5a3aN3a1700750590cd54N3b7ac5c499508501N3b9a3eb233cf81a8N3c6c182814f36fbfN3cc3a8a378c102baN3d7c6148dca4a849N3f3393cd8cbc9f7eN3f87735e66d43351"%lxh.
Ltac2 gd_tbl_P_oid_ec_grp_algid () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.P.P_oid.MBEDTLS_ERR_OID_NOT_FOUND"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.P.PImg.psegs"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.Lib.Cells.C4"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.AStep.statics_ok"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Exec.evt"; "OSSVerify.KrLib.P.P_oid.oid_lookup1_post"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "Stdlib.Lists.List.In"; "Walk.offsets"; "P_OID_EC_GRP_ALGID_TBL"; "OSSVerify.KrLib.Lib.HeapIface.heap_layout"; "OSSVerify.KrLib.P.P_oid.oid_lookup1_stmt"; "P_OID_GET_EC_GRP_ALGID"].


Definition P_OID_GET_EC_GRP_ALGID : Z := 0x249e8.
Definition P_OID_EC_GRP_ALGID_TBL : Z := 0x45298.
Notation OID_EC_GRP_ALGID_TBLN := 80 (only parsing).
Notation OID_EC_GRP_ALGID_STACK := 32 (only parsing).

Section Walk.
  Variable L : heap_layout.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (OID EXT P LEN lo : Z) (tg pd : word) (xs : list byte).
  Hypothesis HLEN : Z.of_nat (length xs) = LEN.
  Hypothesis D1 : EXT + 4 <= OID \/ OID + 24 <= EXT.
  Hypothesis D2 : EXT + 4 <= P \/ P + LEN <= EXT.
  Hypothesis AL1 : OID mod 8 = 0.
  Hypothesis AL2 : EXT mod 4 = 0.
  Hypothesis NZ1 : 0 < OID.
  Hypothesis NZ2 : 0 < EXT.
  Hypothesis NZ3 : 0 < P.
  Hypothesis SLO : lo <= bv_unsigned sp - 32.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis ACP : 4096 < alloc_ceiling.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DS1 : OID + 24 <= lo \/ bv_unsigned sp <= OID.
  Hypothesis DS2 : EXT + 4 <= lo \/ bv_unsigned sp <= EXT.
  Hypothesis DS3 : P + LEN <= lo \/ bv_unsigned sp <= P.
  Hypothesis CA : const_at L P_OID_EC_GRP_ALGID_TBL 80.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis OD : EXT + 4 <= hl_data_lo L \/ hl_data_hi L <= EXT.
  Hypothesis SPR : bv_unsigned sp < 2^64.
  Hypothesis EXTB : EXT + 4 <= 2^64.
  Hypothesis PB : P + LEN <= 2^64.
  Hypothesis OIDB : OID + 24 <= 2^64.

  Notation W := [(EXT, EXT + 4); (bv_unsigned sp - 32, bv_unsigned sp)].
  Notation POST := (oid_lookup1_post psegs L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc EXT 32 lo m).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -32)).
  Notation FRAME mm j := (rw_cells psegs mm (bv_unsigned sp + -32) [CB 8 j; C8 s1; C8 s0; C8 ra]).
  Notation TBLC := P_OID_EC_GRP_ALGID_TBL (only parsing).

  Definition offsets : list Z := [0; 40].

  Lemma exit_walk : ltac2:(CDefT.buildp (gd_tbl_P_oid_ec_grp_algid ()) "Pr,$0.Pv,(1.&40.)Pj,(2.(1.&8.))Px1,(1.&40.)Px5,(1.&40.)Px6,(1.&40.)Px7,(1.&40.)Px8,(1.&40.)Px9,(1.&40.)Px10,(1.&40.)Px11,(1.&40.)Px12,(1.&40.)Px13,(1.&40.)Px14,(1.&40.)Px15,(1.&40.)Px16,(1.&40.)Px17,(1.&40.)Px18,(1.&40.)Px19,(1.&40.)Pmm,P,(1.&40.)(3.(1.&8.))P,(4.(5.$0.R14.=)(5.$0.R14.$6.))P,(7.$8.R2.(9.(:.&40.Vsp,)-20.)(;.$<.(=.#8.R13.)(;.$<.(>.Vs1,)(;.$<.(>.Vs0,)(;.$<.(>.Vra,)(?.$<.))))))P,(10.$8.R3.Vlo,(9.(:.&40.Vsp,)-20.))P,(7.$8.R4.VEXT,(;.$<.(11.R16.)(?.$<.)))P,(12.$8.R5.)P,(13.$8.VL,R6.)P,(14.(;.(15.$0.$0.)(16.$0.$0.VEXT,(9.VEXT,+4.))(;.(15.$0.$0.)(16.$0.$0.(17.(:.&40.Vsp,)+20.)(:.&40.Vsp,))(?.(15.$0.$0.))))Vm,R7.)P,(18.$8.Vm,R8.)(19.$8.(1:.$8.VL,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VEXT,+20.Vlo,Vm,)(1;.(1<.R19.(1=.&40.(9.(:.&40.Vsp,)-20.))Vgp,Vtp,R18.R17.R16.R15.R14.(1=.&40.R1<.)R12.R11.R10.R?.R>.R=.R<.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(1=.&40.+24:70.)Vfc,(1>.(1.&40.))R9.(1?.$8.)))")
(* [comment removed for export] *).
  Proof.
    intros r v j x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 mm Hr FR ST HEXT MI SOK MU WM.
    do 5 zstep.
    release_frame FR ST (bv_unsigned sp). fin.
  Qed.

  Lemma found_walk : ltac2:(CDefT.buildp (gd_tbl_P_oid_ec_grp_algid ()) "Pk,$0.Pv,(1.&40.)Pj,(2.(1.&8.))Px1,(1.&40.)Px5,(1.&40.)Px6,(1.&40.)Px7,(1.&40.)Px8,(1.&40.)Px9,(1.&40.)Px10,(1.&40.)Px11,(1.&40.)Px12,(1.&40.)Px13,(1.&40.)Px14,(1.&40.)Px15,(1.&40.)Px16,(1.&40.)Px17,(1.&40.)Px18,(1.&40.)Px19,(1.&40.)Pmm,P,(1.&40.)(3.(1.&8.))P,(20.$0.R14.$21.)P,(7.$8.R2.(9.(:.&40.Vsp,)-20.)(;.$<.(=.#8.R13.)(;.$<.(>.Vs1,)(;.$<.(>.Vs0,)(;.$<.(>.Vra,)(?.$<.))))))P,(10.$8.R3.Vlo,(9.(:.&40.Vsp,)-20.))P,(7.$8.R4.VEXT,(;.$<.(11.R16.)(?.$<.)))P,(12.$8.R5.)P,(13.$8.VL,R6.)P,(14.(;.(15.$0.$0.)(16.$0.$0.VEXT,(9.VEXT,+4.))(;.(15.$0.$0.)(16.$0.$0.(17.(:.&40.Vsp,)+20.)(:.&40.Vsp,))(?.(15.$0.$0.))))Vm,R7.)P,(18.$8.Vm,R8.)(19.$8.(1:.$8.VL,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VEXT,+20.Vlo,Vm,)(1;.(1<.R19.(1=.&40.(9.(:.&40.Vsp,)-20.))Vgp,Vtp,R18.R17.R16.R15.(1=.&40.VEXT,)R13.(1=.&40.(9.$22.R1<.))R11.R10.R?.R>.R=.R<.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(1=.&40.+24:64.)Vfc,(1>.(1.&40.))R9.(1?.$8.)))")
(* [comment removed for export] *).
  Proof.
    intros k v j x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 mm Hk FR ST HEXT MI SOK MU WM.
    unfold P_OID_EC_GRP_ALGID_TBL in *.
    destruct Hk as [<-|[<-|[]]]; cbn [Z.add].
    all: lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?e) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
           let a := eval vm_compute in (e + 32) in
           let bs := eval vm_compute in (match image_bytes psegs a 4 with Some bs => bs | None => [] end) in
           pose proof (statics_ok_cells psegs L mm a bs SOK ltac:(eapply const_at_sub; [exact CA| cbn; lia| cbn; lia]) ltac:(vm_compute; reflexivity)) as TB;
           cbn [length] in TB
         end.
    all: zstep; zstep; clear TB; zstep; eapply exit_walk; try eassumption; left; reflexivity.
  Qed.

End Walk.

Ltac found kk :=
  let a := eval vm_compute in (0x45298 + kk) in
  replace (Z_to_bv 64 a) with (Z_to_bv 64 (P_OID_EC_GRP_ALGID_TBL + kk)) by reflexivity;
  eapply found_walk with (k := kk); try eassumption; try solve_in; try plia.
Ltac notfound := eapply exit_walk; try eassumption; right; reflexivity.

Ltac flia := first [clear_disj; lia | lia].
(* [comment removed for export] *)
Ltac ro_const' A0 n0 RO :=
  lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom ?sg)] =>
    let cbs := eval vm_compute in (match image_bytes sg A0 n0 with Some cbs => cbs | None => [] end) in
    match goal with MI : mem_inv sg mx |- _ =>
      pose proof (ro_image_bytes_at sg mx A0 cbs MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO;
      let nz := eval vm_compute in (Z.of_nat n0) in let ROL := fresh "ROL" in assert (ROL : Z.of_nat (length cbs) = nz) by reflexivity end
  end.

Lemma P_oid_get_ec_grp_algid_spec : ltac2:(CDefT.buildp (gd_tbl_P_oid_ec_grp_algid ()) "PL,$23.(24.$8.R1.$25.$22.+50.+20.)")
(* [comment removed for export] *).
Proof.
  intros L. unfold oid_lookup1_stmt, P_OID_GET_EC_GRP_ALGID.
  intros until xs. intros HOID HXS HLEN HEXT D1 D2 AL1 AL2 NZ1 NZ2 NZ3 ST SLO ACL SPA DS1 DS2 DS3 MI SOK CA DHI OD -> ->.
  pose proof alloc_ceiling_pos as ACP.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (rw_cells_bound _ _ _ _ HEXT) as EXTB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in EXTB.
  change (Z.of_nat 4) with 4 in EXTB.
  pose proof (rw_cells_bound _ _ _ _ HOID) as OIDB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ buf_cells] in OIDB.
  change (Z.of_nat 24) with 24 in OIDB.
  pose proof (bytes_at_bound _ _ _ _ HXS) as PB. rewrite HLEN in PB.
  unfold buf_cells in HOID.
  assert (LEN0 : 0 <= LEN) by lia.
  (* [comment removed for export] *)
  assert (LXSUMS : forall AL, Forall (summary_ok psegs AL) [SUM_bcmpCP 0x43248])
    by (intros AL; repeat constructor; apply sum_bcmpCP_ok; exact P_bcmp_spec).
  lx_run_tac (PLANS [0x24a00] [] 40%N (@nil summary)); lx_tree.
  all: lazymatch goal with E : @eq mem ?mx ?mc0 |- _ => subst mx | |- _ => idtac end.
  1: { (* [comment removed for export] *) fin; try (right; reflexivity); try apply munch_refl; try apply wmono_refl. }
  repeat match goal with H : munch [] ?a ?a |- _ => clear H | H : wmono _ ?a ?a |- _ => clear H end.
  repeat match goal with H : stk _ m lo ?x, H' : stk _ m lo ?x |- _ => clear H' end.
  repeat match goal with H : mem_inv _ m, H' : mem_inv _ m |- _ => clear H' end.
  lazymatch goal with Hs : stk _ m lo _ |- _ => carve_frame 32%nat Hs end.
  lazymatch goal with Hf : rw_cells ?sg m ?A [CB 32 ?j] |- _ =>
    set (JJ := j) in Hf; clearbody JJ; change (rw_cells sg m A ([] ++ CB 32 JJ :: [])) in Hf;
    apply (rw_cells_split_CB sg m A [] 32 JJ [] [8; 24]%nat) in Hf; [| reflexivity]; cbn [mk_CB_cells app] in Hf end.
  lx_run_tac (PLANS [0x24a10] [] 20%N (@nil summary)); lx_tree.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  lazymatch goal with Hi : mem_inv _ m1 |- _ => rename Hi into MI1 end.
  repeat match goal with H : mem_inv _ m |- _ => clear H end.
  ro_const' 0x10556 3%nat RO1. ro_const' 0x10724 3%nat RO2.
  lx_run_tac (PLANS [0x24a70; 0x24a64] [] 120%N [SUM_bcmpCP 0x43248]); lx_tree.
  all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ ?mx _) =>
       lazymatch goal with Hm : munch ?W1 ?mq mx |- _ =>
         let MUW := fresh "MUW" in
         assert (MUW : munch [(EXT, EXT + 4); (bv_unsigned sp - 32, bv_unsigned sp)] m mx)
           by (eapply munch_weaken; [| exact Hm]; intros xw Hxw; clear -Hxw; cbn in Hxw |- *; lia);
         pose proof (statics_ok_munch psegs L _ _ _ SOK MUW ltac:(intros a Ha NW; clear -Ha ACL SLO DHI OD; cbn; lia)) as SOKx
       end end.
  all: first [ lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x24a70) _ _ _ _) => notfound end
             | lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?az) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
                 let kk := eval vm_compute in (az - 0x45298) in found kk end ].
Qed.
