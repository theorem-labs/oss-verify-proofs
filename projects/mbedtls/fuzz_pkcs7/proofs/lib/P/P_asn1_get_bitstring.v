(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_asn1_get_tag.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00299e69dc803829 0 2 0 1 1 1P010a510d09a917a4 0 5 0 1 11 1 12 1 14 1 17 1P0148352c02b19d08 0 4 0 1 9 1 11 1 14 1P0189622bbdac6c8c 0 2 0 1 2 1P039fb27ffd9a2520 0 4 0 1 13 1 15 1 16 1P04f3de5ff342c8c0 0 2 0 1 19 1P0585cfd7e1b7b41e 0 2 0 1 21 1P06865d3c9edcb39c 0 4 0 1 12 1 14 1 17 1P06e99d96dd1d2322 0 2 0 1 2 1P08dddceaaeb929f7 0 2 0 1 11 1P0a48d4ac8b9752d4 0 2 0 1 1 1P0a6b1bd91f4cf636 0 3 0 1 10 1 15 1P0c372ce17445180a 0 2 0 1 32 1P0ddf8d27a1fc1d5e 0 2 0 1 1 1P10435f66773a1e7a 0 5 0 1 14 1 17 1 18 1 20 1P10dc4632315303aa 0 2 0 1 2 1P11ff0ff0f0e7e03c 0 2 0 1 28 1P12dfc4f246d81491 0 5 0 1 11 1 13 1 15 1 16 1P12e4cfbfe34a2c81 0 3 0 1 1 1 24 1P17215ab80eb1c5e8 0 2 0 1 5 1P18821187477c231e 0 2 0 1 33 1P18c53d71486a72d0 0 2 0 1 26 1P18f1367e6321dd43 0 2 0 1 5 1P19a383c7b92eb857 0 3 0 1 4 1 23 1P1a92ccda12b0bed5 0 2 0 1 31 1P20f2b952c5b52ff7 0 2 0 1 32 1P2109c58757a8032f 0 5 0 1 20 1 23 1 24 1 26 1P21eceed49c59a9f8 0 6 0 1 10 1 13 1 14 1 15 1 16 1P27977dcd22b0b58a 0 4 0 1 12 1 14 1 17 1P28ad59f8316ec143 0 2 0 1 1 1P2c14bfe07ed88093 0 2 0 1 25 1P2d633f6cce7c80eb 0 3 0 1 11 1 17 1P2e37d413f26473d4 0 4 0 1 13 1 15 1 16 1P2fc8f9d895f1f02a 0 3 0 1 20 1 26 1P3129b4f64d320714 0 5 0 1 19 1 22 1 23 1 25 1P31a41dbb8abe5dd3 0 2 0 1 9 1P31bf20e7d744a4b1 0 5 0 1 11 1 12 1 14 1 17 1P34b0618447ad8ec6 0 4 0 1 1 1 16 1 22 1P382ae041bee0a0e0 0 2 0 1 2 1P394f8aa1a998c962 0 5 0 1 11 1 13 1 15 1 16 1P39f20ac33014d6f5 0 4 0 1 6 1 23 1 24 1P3c184c6ed2c84faf 0 3 0 1 1 1 19 1P3cb97622843ea854 0 2 0 1 11 1N0019f211551aacd1N0112467cdbfc2ec5N01c3b250178da138N01e642a5a68fdbb3N024d4aa72708e109N026afc7a6ad50fb6N029171b937839354N02b41ebca562c2ebN02d4cc31481f4bcdN03b27901f30b3fe3N03bf901cc56b3c3eN0408a78ef4e8a90bN042838fe4b81309dN046de7fe20a8a818N04e4c7dc1069711dN053cf2d226560732N0574ab8ab7f642dbN05823675da4b1718N064bf373c3e8046dN06be8d47c80d7a3eN071465c9c8e6acafN07c78d35ba33aab7N095350c0ab51f3c8N097a59b52fa0ddf2N09c456bbce1a4e85N09e563c55f62e8a5N0a0c026dc80afb77N0a6cf6c41bae9a94N0a9448df5ebb3b24N0acc3f38444f3a52N0acdec57fa1d5a21N0b26a4cec679eb6eN0b536320348461fbN0bc3026cc1176d50N0c1f6531185bd716N0c52fc566a43d158N0d8ebaede92836e1N0dfabc14bb265de0N0e3d7e190c19f009N0f65151749d04a7fN0f898d8bf6890c6bN102bc1a1de2e5314N10d40e997d03dd73N11645d28ee531c28N11bf3d286fb2f6f5N126286c3d4ff89c4N126da65299c438f6N12cc12036f09f686N12f1e838f7a4c3e0N13169f597fb05309N1331816cae5aa6ceN13a5ed9e7e6ee774N143903b0eef7d690N152d81f19496e5e7N153ee31b9bb38505N15597b68ea5f5382N158a16a12e3390f9N15ba2b782c0d8e1aN15bac05bdc2547faN15eb82be7436f5aeN162759d8cacfef9eN162feac0cce24e69N163025bd085a5004N1697683227a9032bN16a5dcb0faa941bbN16cab44b3967ab60N16d3be2367782129N171e4ffd0d196e93N172bf7d7bc688cf3N17519f9aee2bdec5N175755241a9370f9N17fc3f4523cf5dbaN180032aab6410d88N185a405158c689ebN1890422c2a6c97eeN18c60eaf3ebbf679N18eed4e257507fb8N195ab7f6ac329794N1963f15936b53e78N1a1d4aaf6eaadb94N1a3a93d6c0763552N1a5bb6b03fa8936cN1ab897f8483ca2d9N1ad039648c0f4504N1b95fb0a673e7c5cN1bab932c25ba4842N1bebabe398911f1aN1c3341844ef140f7N1d0414fa01379f5fN1d168ca4efdddeb9N1d1db5cbbad7d2d9N1d418475bc6e1cc1N1d692047474dd025N1ddad8c82e4b39b7N1dee079e7db6169cN1e88ca6f989febf2N1eacbf08e938dc55N1ece80dd3668219cN1ee99acc63576a76N1f2c1ae319901109N1f4241c639083875N1f8bdbd18e6f6f0dN1fadf5d37e84b263N1fd753b98eca0512N206948f141e93e4aN208c4963feeb3973N2176707c553d42c9N22118e038423c0ddN2213c184ed10d913N22ce73f0bf3f618eN23f7306afecf93b8N2415cc5e91c370bdN24541fb53b70941bN24b01729d9479d3dN2566575a4db4430bN259d1c91eea626e0N25ab8aab8c969165N25f9e3ef4ec3c7e1N26010103994dfe8fN26159d485d527f57N261c8eebf244d090N265db228b22916d9N2661a8b7c5098012N268c5781e5db95e0N26cc65212a496a83N26fca5c98a8fcd15N272a1ccd4b893f55N273becc617820d96N278cc5fe779360aeN27a0d34b39cbdb4dN28487955de351d43N2865575af1aee0f6N28c591ff5ab504c8N28d9457247d79d2eN2921bd9ff4f42294N299ed4f289e9398aN2b8055012f60b20aN2bde9dfbb3cdc888N2c4c64ae51115457N2d48b348588f9a1cN2d6679cc811f9321N2d7cb3c154e5feedN2d8a9d7a10ca4cfdN2de0ffd0db4864ffN2de643ea4aa99578N2dfb1693ffdbed3cN2e24e805f8377354N2e6b18c728b9cbffN2e8e3c67eb527e5eN2ec52c27c21dd0a4N2f0c96de812bdd40N2f7d8e3732618162N2f8304e384d14902N2fa6b753aedac798N2fd70699bd0530caN2fef9d14a2a9c44cN3022824fdf2f57b2N30558bbc8f8edeecN3056ff5dec722cd5N30f7e68c03da8f8aN30f871dca36c4dc1N3104e71dda6f1023N315b50a7dd21eb68N31635365bd05ebaaN317a6a035dbf8da6N3181d6d2b33ac429N31a10c991bcaad92N31dbe1ccb2685ec3N32f8f908f77431eeN33725645615f6d42N33ab474928e54ed2N340d5742194940a0N34181b6c9bd90ddeN3422d73c0d6cd67cN34a9e74d51f0f256N34b863a44d64e336N34d80cd86ca7bad7N354028587f02cce9N366bd1ef1331fa3bN367c5439bee98db4N36b39f282bbaf9b2N36bbedf6b060f232N3730fcfdc3d3f3d6N374a4b5c0df3f875N37e87f1d4facc8c3N37f01cb85672edadN38b8dbfe03a2e486N38e002a81a30d8cdN38f1b91104b4a483N3943ef9af0b09ac8N3957a2ba74bf7d22N39ede63f954611e3N3a1c1ac854a3dfadN3a7800256443019cN3a7b3a099e65b3bcN3ab004b1405b0a9bN3ad681e5851d1ce3N3ae6dc819c488cb3N3ba466ce16ed7815N3ba9045c7d2c8749N3bbc3b4040cc5fdfN3bc325a6c2eb9479N3bdc4b16ac1ad188N3bec0e78e7555a80N3cad070943099295N3cb0319a718e7059N3cd21ca8b2f4a1a7N3d749abf2c2e35a5N3e37fe071af5022bN3e8aff95951f01bbN3ed64dc5ba4fb886N3f7968454596ee9bN3fc6a6fb0c15d005N3fd190c6865d6e72N3fd24bd6290ce770N3fe2bd88bd3147f6"%lxh.
Ltac2 gd_tbl_P_asn1_get_bitstring () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "bitstring_cells"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.P.PImg.psegs"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.Lib.Exec.evt"; "asn1_get_bitstring_post"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.to_nat"].


Definition P_ASN1_GET_BITSTRING : Z := 0x1e270.

(* [comment removed for export] *)
Notation ASN1_GET_BITSTRING_STACK := 32 (only parsing).

Definition bitstring_cells (len : word) (ub : byte) (pad : list byte) (p : word) : list cell :=
  [C8 len; C1 ub; CB 7 pad; C8 p].

Definition asn1_get_bitstring_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PP BSP P END BUF lo : Z) (pad : list byte) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_bitstring ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lr,$4.(1.$4.Lp',$4.(1.(2.&40.)LL,(2.&40.)(1.(2.&8.)Lub,(2.&8.)(1.(2.&40.)Lpw,(2.&40.)(5.(6.$0.R16.(7.(8.O1:.O19.O18.O17.R15.R14.R13.O16.O15.R12.R11.R10.R?.R>.R=.R<.R;.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.R:.R9.R8.R7.)O:.(9.O1:.)O9.(:.(2.&40.))R6.(;.O1;.)))(5.(<.(=.(>.$4.$4.)(?.$4.$4.O8.(10.O8.+8.))(=.(>.$4.$4.)(?.$4.$4.O7.(10.O7.+18.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.O19.)+20.)(12.&40.O19.))(13.(>.$4.$4.)))))O1.R6.)(5.(14.O1;.O1.R6.)(5.(15.O1;.R6.)(5.(6.(2.&40.)R12.(16.&40.R5.))(5.(5.(17.-7?.R5.)(18.R5.=))(5.(19.O1;.R6.O8.(=.$1:.(1;.(16.&40.R4.))(13.$1:.)))(5.(19.O1;.R6.O7.(1<.R3.R2.O2.R1.))(5.(1=.O1;.R6.O3.(12.&40.O19.))(5.(5.(18.O6.R4.)(18.R4.O5.))P,(6.$4.R5.=)(1.$4.Lq,$4.(5.(6.(2.&40.)R3.(16.&40.R1.))(5.(18.(10.O6.+3.)R1.)(5.(6.$4.(10.R1.(12.&40.R5.))R6.)(6.$4.R6.O5.))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition asn1_get_bitstring_stmt {L : heap_layout} (segs : list Segment) (ENTRY : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (PP BSP P END BUF lo : Z) (bs : list byte) (lenv : word) (ubv : byte) (pad : list byte) (pv : word),
  rw_cells segs m PP [C8 (Z_to_bv 64 P)] ->
  rw_cells segs m BSP (bitstring_cells lenv ubv pad pv) ->
  bytes_at segs m BUF bs ->
  BUF <= P -> P <= END -> END <= BUF + Z.of_nat (length bs) -> BUF + Z.of_nat (length bs) < 2^63 ->
  (PP + 8 <= BSP \/ BSP + 24 <= PP) ->
  (PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP) ->
  (BSP + 24 <= BUF \/ BUF + Z.of_nat (length bs) <= BSP) ->
  (* [comment removed for export] *)
  PP mod 8 = 0 -> BSP mod 8 = 0 -> 0 < PP -> 0 < BSP -> 0 < BUF ->
  (* [comment removed for export] *)
  stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ASN1_GET_BITSTRING_STACK -> alloc_ceiling <= lo ->
  bv_unsigned sp mod 16 = 0 ->
  (PP + 8 <= lo \/ bv_unsigned sp <= PP) ->
  (BSP + 24 <= lo \/ bv_unsigned sp <= BSP) ->
  (BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF) ->
  mem_inv segs m ->
  a0 = Z_to_bv 64 PP -> a1 = Z_to_bv 64 END -> a2 = Z_to_bv 64 BSP ->
  evt segs (asn1_get_bitstring_post segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP BSP P END BUF lo pad m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).

Section Walk.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP BSP P END BUF lo : Z) (bs : list byte) (pad : list byte).
  Hypothesis B1 : BUF <= P.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= BSP \/ BSP + 24 <= PP.
  Hypothesis D2 : PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D3 : BSP + 24 <= BUF \/ BUF + Z.of_nat (length bs) <= BSP.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis BSB : 0 <= BSP /\ BSP + 24 <= 2^64.
  Hypothesis BUF0 : 0 <= BUF.

  Notation W := [(PP, PP + 8); (BSP, BSP + 24); (bv_unsigned sp - ASN1_GET_BITSTRING_STACK, bv_unsigned sp)].
  Notation POST := (asn1_get_bitstring_post psegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP BSP P END BUF lo pad m).

  (* [comment removed for export] *)
  Lemma j1_walk : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_bitstring ()) "Pp1,$4.PL,(2.&40.)Ppv,(2.&40.)Pubv,(2.&8.)Px5,(2.&40.)Px15,(2.&40.)Px17,(2.&40.)Pmm,P,(2.&40.)(3.(2.&8.))P,(5.(18.(10.VP,+2.)R8.)(18.R8.VEND,))P,(19.$1>.R2.VPP,(=.$1:.(1;.(16.&40.R9.))(13.$1:.)))P,(19.$1>.R3.VBSP,(1<.R9.R7.Vpad,R8.))P,(1?.$1>.R4.VBUF,Vbs,)P,(1=.$1>.R5.Vlo,(12.&40.Vsp,))P,(<.(=.(>.$4.$4.)(?.$4.$4.VPP,(10.VPP,+8.))(=.(>.$4.$4.)(?.$4.$4.VBSP,(10.VBSP,+18.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.Vsp,)+20.)(12.&40.Vsp,))(13.(>.$4.$4.)))))Vm,R6.)P,(14.$1>.Vm,R7.)P,(15.$1>.R8.)(20.$1>.(21.$1>.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VBSP,VP,VEND,VBUF,Vlo,Vpad,Vm,)(7.(8.Vra,Vsp,Vgp,Vtp,R<.Vt1,Vt2,Vs0,Vs1,(16.&40.-60.)(16.&40.VEND,)(16.&40.VBSP,)(16.&40.VPP,)(16.&40.R10.)R;.R?.R:.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(16.&40.+1>2;8.)Vfc,(:.(2.&40.))R9.(;.$1>.)))")
(* [comment removed for export] *).
  Proof.
  (* [comment removed for export] *)
  intros p1 L pv ubv x5 x15 x17 mm Hp HPP HBS HBUF ST MU WM MI.
  try (unfold bitstring_cells in HBS).
  pose proof (bv_unsigned_in_range 64 L) as LR.
  try (unfold bv_modulus in LR).
  try (cbn in LR).
  lxp_run (PLAN [0x1e270; 0x1e32c] [(0x1e374, DMerge 10); (0x1e580, DMerge 5)] 232%N).
  (* [comment removed for export] *)
  all: first [ lxp_ret ].
Qed.

  (* [comment removed for export] *)
  Lemma loop1_walk : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_bitstring ()) "Pk,$22.Pcur,$4.Pstop,$4.PL,(2.&40.)Ppv,(2.&40.)Pubv,(2.&8.)Px5,(2.&40.)Px17,(2.&40.)Pmm,P,(2.&40.)(3.(2.&8.))P,(6.$22.(23.(11.R7.R8.))R9.)P,(5.(18.(10.VP,+2.)R9.)(17.R9.R8.))P,(18.R9.VEND,)P,(19.$1>.R4.VPP,(=.$1:.(1;.(16.&40.R;.))(13.$1:.)))P,(19.$1>.R5.VBSP,(1<.R:.R8.Vpad,R9.))P,(1?.$1>.R6.VBUF,Vbs,)P,(1=.$1>.R7.Vlo,(12.&40.Vsp,))P,(<.(=.(>.$4.$4.)(?.$4.$4.VPP,(10.VPP,+8.))(=.(>.$4.$4.)(?.$4.$4.VBSP,(10.VBSP,+18.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.Vsp,)+20.)(12.&40.Vsp,))(13.(>.$4.$4.)))))Vm,R8.)P,(14.$1>.Vm,R9.)P,(15.$1>.R:.)(20.$1>.(21.$1>.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VBSP,VP,VEND,VBUF,Vlo,Vpad,Vm,)(7.(8.Vra,Vsp,Vgp,Vtp,R=.Vt1,Vt2,Vs0,Vs1,(16.&40.-60.)(16.&40.VEND,)(16.&40.VBSP,)(16.&40.VPP,)(16.&40.R12.)(16.&40.R11.)R10.R<.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(16.&40.+1>32<.)Vfc,(:.(2.&40.))R;.(;.$1>.)))")
(* [comment removed for export] *).
  Proof.
  (* [comment removed for export] *)
  induction k as [|k IH]; intros cur stop L pv ubv x5 x17 mm Hk Hcur Hstop HPP HBS HBUF ST MU WM MI; [lia|].
  try (unfold bitstring_cells in HBS).
  destruct (nth_error bs (Z.to_nat (cur - BUF))) as [b|] eqn:NB; [| apply nth_error_None in NB; lia].
  read_at HBUF NB (cur - BUF) RD.
  lxp_run (PLAN [0x1e270; 0x1e2b8; 0x1e32c] [(0x1e374, DMerge 10); (0x1e580, DMerge 5)] 232%N).
  (* [comment removed for export] *)
  all: first [ lxp_at 123692; (lxp_apply (IH (cur + 1) stop)) | lxp_at 123576; (first [ solve [ lxp_apply j1_walk ] | solve [ eapply j1_walk with (p1 := cur + 1); lxp_apply_post; lxp_apply_post ] | lxp_apply j1_walk ]) ].
Qed.

  Lemma loop1_entry : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_bitstring ()) "Pnn,$4.Pstopw,(2.&40.)Ppv,(2.&40.)Pubv,(2.&8.)Px5,(2.&40.)Px17,(2.&40.)Pmm,P,(2.&40.)(3.(2.&8.))P,(5.(18.+1.R7.)(18.R7.+4.))P,(18.(10.(10.VP,+2.)R8.)VEND,)P,(6.(2.&40.)R8.(16.&40.(10.(10.VP,+2.)R9.)))P,(19.$1>.R4.VPP,(=.$1:.(1;.(16.&40.(10.VP,+2.)))(13.$1:.)))P,(19.$1>.R5.VBSP,(1<.(16.&40.=)R8.Vpad,R9.))P,(1?.$1>.R6.VBUF,Vbs,)P,(1=.$1>.R7.Vlo,(12.&40.Vsp,))P,(<.(=.(>.$4.$4.)(?.$4.$4.VPP,(10.VPP,+8.))(=.(>.$4.$4.)(?.$4.$4.VBSP,(10.VBSP,+18.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.Vsp,)+20.)(12.&40.Vsp,))(13.(>.$4.$4.)))))Vm,R8.)P,(14.$1>.Vm,R9.)P,(15.$1>.R:.)(20.$1>.(21.$1>.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VBSP,VP,VEND,VBUF,Vlo,Vpad,Vm,)(7.(8.Vra,Vsp,Vgp,Vtp,R=.Vt1,Vt2,Vs0,Vs1,(16.&40.-60.)(16.&40.VEND,)(16.&40.VBSP,)(16.&40.VPP,)(16.&40.(10.VP,+2.))R10.(16.&40.=)R<.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(16.&40.+1>32<.)Vfc,(:.(2.&40.))R;.(;.$1>.)))")
(* [comment removed for export] *).
  Proof.
    intros nn stopw pv ubv x5 x17 mm HN HE -> HPP HBS HBUF ST MU WM MI.
    eapply loop1_walk with (k := Z.to_nat nn) (cur := P + 2) (stop := P + 2 + nn); try eassumption; lia.
  Qed.
End Walk.

Lemma P_asn1_get_bitstring_spec {L : heap_layout} : asn1_get_bitstring_stmt psegs P_ASN1_GET_BITSTRING.
Proof.
  (* [comment removed for export] *)
  unfold asn1_get_bitstring_stmt, P_ASN1_GET_BITSTRING.
  intros until pv.
  intros HPP HBS HBUF B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 ST SLO ACL SPA DS1 DS2 DS3 MI -> -> ->.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB.
  pose proof (rw_cells_bound _ _ _ _ HBS) as BSB.
  cbn [bitstring_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in PPB, BSB.
  pose proof (proj1 HBUF) as BUF0.
  pose proof (munch_refl [(PP, PP + 8); (BSP, BSP + 24); (bv_unsigned sp - ASN1_GET_BITSTRING_STACK, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  try (unfold bitstring_cells in HBS).
  lxp_run (PLAN [0x1e2b8; 0x1e32c] [(0x1e374, DMerge 10); (0x1e580, DMerge 5)] 232%N).
  (* [comment removed for export] *)
  all: first [ lxp_at 123692; lxp_longform nn; (first [ solve [ lxp_apply loop1_entry ] | solve [ eapply loop1_entry with (nn := nn); lxp_apply_post; lxp_apply_post ] | lxp_apply loop1_entry ]) | lxp_at 123576; (first [ solve [ lxp_apply j1_walk ] | solve [ eapply j1_walk with (p1 := P + 2); lxp_apply_post; lxp_apply_post ] | lxp_apply j1_walk ]) | lxp_ret ].
Qed.

