(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require BJ0Gc2. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep TacX ZBridge Exec CellsX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs RMalloc_iface_stmt F_memcmp F_memset.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog StrFun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require Import BJRep BJFrame HeapMF_iface BJHeap BJIface BJIfaceObj BJIfaceObjL BJKitVS BJKitW BJKitStr BJKitDtor BJKitIn BJKitObj
     W_dtor_value W_dtor_value2 W_octor W_num0 W_octorL.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import StoreDj.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes03nat37Corelib7Numbers7BinNumshd1Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Refh2RMalloc_iface_stmt~~~~~~ja3mem37Corelib4Init5Logicoa3and46Stdlib6ZArith6BinInt1Zq43addq42leoa2exhd4Npos79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~t34cellq42lt35stdpp9bitvectorbdefinitionshhb2bv04cons04list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~hka2wzoa2eqoa2ort32C479OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~hpa5rsegsq46of_natq43pow06length03nil69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~hvb5hceilt32C8t32CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ik98bytes_at79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~iof8rw_cellsq43mul89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ9W_octorL24HCW2~~~~~~itc8slots_ok06option79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~jj43ivljj45munchjj45wmono3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsjo9dmachine_state3h5LinuxProcessSemantics5Riscv7Preludejt15bvmaphhb7Z_to_bv04Nonejj43mkR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~kh82MSik97mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~km67seg_romitc9walk_post79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~krd3evt37Corelib5Lists7ListDefkvf3map37Corelib4Init3Natlhd3mulitc7bkcellst3acells_size03app01S37Corelib4Init5Peanoll62ltkvf6firstnkvf3nthkvf5skipnjj4ddisjoint_fromlhd3subkvf6Forallkvf6repeatt3bcells_bytesll62le79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ8W_octorL~~~~~~lsa8OCL_KMULlsabocL_scratchitcaprobe_postjacrblock_rangeq44land" s.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section HCW2.
  Context {HCEIL : HeapCeil}.
  (* [comment removed for export] *)
  Definition slots_ok : ltac2:(zQ "30!h8!j6!o4>1m$2>1T$1>1k$0P") := ltac2:(zQ "hc0!pe!j6!rc!s2!s7!sc!hgf!hh6!hj8!hje!hk4!ho5!hob!hp0!hp5!ht6!htf!hu8!hue!h8!hv6!ij6!ijf!ik4!io3!isa!o4!it6\1m$ha\1T$1\1k$h3>1j$1>0@2$0@2$3Z^1@2$7^1@1$h0^2@2$4@1$a@1$8@1$5#8\2hb@1$a@1$8@1$5#8@2$4$1\2Kj$1@2$4$1\4lenj$1@2$4$1\3nxj$1@2$4@1$a@1$8@1$5#8\3kbj@1$a@1$8@1$5#8@2$0@4$h9$f^a@2$2@2$2^9+h0@2$hb+i8^7@3$9$6@2$h7Nh8^5@3$9$6@1$h6@1$b^4@3$9$6@1$e@1$b^3@3$9$6@1$e@1$b^2@1$h4$6@2$0@2$0@2$3Z^3@2$7^3@2$h1+2+hf@2$0@2$0@2$3Z^2@2$7^2@2$h1+2+i0@2$0@2$d@3$c$1^2+vvvvvvvf@2$7^2^7@2$0@4$h8$f^a^4^1@2$0@3$c$1@1$h0@2$h2@1$8@1$5#8^1@2$2^3+1@2$0@2$7Z^4@2$0@2$3@2$2^4@2$2^3+1@1$h5?5HCEIL@2$d@2$3@2$2^4@2$2^3+1+hggg0@2$3+hitgg0^4").

  Lemma slots_ok_transport : ltac2:(zQ "c0!sc!ji0!hj8!h8!hv6!jic!j6!jn0!jn7!jo0!o4!ht6>1m$a>2m'>0@1$2@1$0#k0@1$5@1$2@1$0#8>1T$6>1k$3>0@3$1^4^2^1>0@3$8@1$4$7^5^4>0@3$9$b^6^5@3$1^6^5^4").
  Proof.
    intros m m' T k SL MU WM j Hj. ndestruct (SL j Hj) as (hb & Kj & lenj & nxj & kbj & R & L & NX & NXJ & KB & LKB & K0 & KH & KR).
    nexists hb, Kj, lenj, nxj, kbj. split; [eapply rw_cells_transport; [exact R| exact MU| exact WM| exact I]|].
    split; [exact L|]. split; [exact NX|]. split; [exact NXJ|]. split; [eapply bytes_at_transport; [exact KB| exact MU| exact I]|]. repeat split; assumption.
  Qed.

  (* [comment removed for export] *)
  Definition walk_post : ltac2:(zQ "70!sc!hj8!j6!h8!js0!jv7!o4>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$5@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1T$2>3len$2>1k$3>1m$6>0$4P") := ltac2:(zQ "i62!sc!hj8!s7!pe!j6!rc!hob!hgf!s2!hje!ht6!ho5!hh6!kg0!hk4!hv6!jic!hp0!js0!hp5!it6!kgb!h8!jv7!ij6!ijf!ik4!jn0!kh1!jn7!jo0!kl5!klb!kq5!isa!o4!htf!hu8&>0@1$1@1$0#k0@1$h0@1$1@1$0#8&@2$5@2$5^hd+h0@2$h4+i8^4\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h7@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1T$4\3len$4\1k$h6\1m$i3\2ms$h2@2$2@1$1@1$0#k0\3ra'@1$1@1$0#k0@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2s4@1$1@1$0#k0@2$2@1$1@1$0#k0\2s5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2$4\3pc'$4@2$3@3$6$h2^h5@7$hf@hf$hc^h4^i8^i7^i6^h3^h2^h1^i5^i4^h0^f^e^d^c^b^a^9^i3^i2^8^7^i1^i0^hf^he^hd^hc^6^5^4^3^hb@2$d@1$0#k0^1^ha@1$h5@1$1@1$0#k0^2@1$i1$a@2$3@3$hd@1$f$hb^h6^2@2$3@3$he$a^h6^2@2$3@2$i0$a^2@2$h1@3$6$4^1+krjq8@2$3@3$6$4^1+krlsc@2$2$4\1j$4@2$2@1$e@1$1@1$0#8\2hb@1$e@1$1@1$0#8@2$2$4\2Kj$4@2$2$4\3nxj$4@2$3@2$3@2$8Z^4@2$c^4@1$i4^hb@2$3@3$6@1$1@1$0#k0^c@2$d@1$0#k0~1@2$3@3$6@1$1@1$0#k0^b@2$d@1$0#k0^2@2$3@4$i2$a^6~1@3$9$7@2$haNh8^3@3$9$7@1$h9@1$b^2@3$9$7@1$h3@1$b^hc@3$9$7@1$h3@1$b^1@1$f$7@2$3@2$3@2$8Z^1@2$c^1@2$i5+2+i0@2$3@2$cZ^2@2$3@2$8@2$5^2@2$5^hc+1@1$h8?5HCEIL@2$h1@2$8@2$5^2@2$5^hc+1+hggg0@2$8+hitgg0^2").

  Lemma oL_walk : ltac2:(zQ "hb0!sc!hj8!kg0!j6!hh6!s2!htf!ht6!rc!hu8!h8!pe!kgb!hue!hk4!jv7!ji0!kr0!ij6!kv8!kh1!kl5!io3!klb!kq5!o4!it6>1d$a>1i$3>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s8@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$f@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$h9>1T$3>1K$3>3len$3>1E$3>1S$3>1k$a>2kb@1$e@1$1@1$0#8>0@2$h7$7^8>0@2$4^i3@1$6^i4>0@2$b@2$5Z^i4@2$4^i4@1$6^4>0@2$4@1$6^5@2$9+2+ha>0@2$4Z^b>0@2$5@2$8@2$8^c+h0@2$ha+i8@1$6^7@1$h2?5HCEIL>0@4$h6$7^e^c^7>0@2$5^c@1$6@2$d@1$1@1$0#8^8>0@2$b@2$5Z^d@2$4^d@2$9+2+hf>0@2$5Z^f>0@2$4^h0@2$9+2+k0>0@3$h0^h3^h2^d@3$h3$7@h3$h1^ic^ib^ia^i6@2$2@1$0#k0^h0@2$2@1$0#k0^h2@2$2@1$0#k0^h1@2$2@1$0#k0^f@2$2@1$0#k0@2$8^h3+h0^hc@2$2@1$0#k0+vvvvvvvf@2$2@1$0#k0+i8^hb^h6^h5^h3^h1^e^h4@7$h5@hf$h4^id^ic^ib^ia^i9^i8^i7^i6@2$2@1$0#k0^h0@2$2@1$0#k0^ie^i5^i4^i3^i2^i1^i0^hf@2$2@1$0#k0^h2@2$2@1$0#k0^h1^he^hd@2$2@1$0#k0^f@2$2@1$0#k0@2$8^h3+h0^hc@2$2@1$0#k0+vvvvvvvf@2$2@1$0#k0+i8^hb^ha^h9^h8^h7^h6@2$2@1$0#k0+krlq0^h5@1$c@1$1@1$0#k0^h4@1$h8$7").
  Proof.
    induction d as [|d IH]; intros until kb; intros MI ID IK K26 T0 TH KB LKB LEN K0 KHI SL; [lia|]. hcb.
    ndestruct (SL i IK) as (hb & Kj & lenj & nxj & kbj & R & L & NX & NXJ & KBJ & LKBJ & KJ0 & KJH & KJR).
    assert (NEXT : forall (ra' a0' a1' a2' a3' a4' a5' a6' a7' s5' t0' t1' t2' t3' t4' t5' t6' : word) m',
      munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> bytes_at rsegs m' K kb ->
      evt rsegs (walk_post sp gp tp s0 (Z_to_bv 64 E) (Z_to_bv 64 K) (Z_to_bv 64 len) (Z_to_bv 64 S) (Z_to_bv 64 (T + 16)) s8 (Z_to_bv 64 4294967295) (Z_to_bv 64 40) s11 F fc T len k m)
        (MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 E) a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 K) (Z_to_bv 64 len) (Z_to_bv 64 (T + 16 + 40 * i)) s5' (Z_to_bv 64 S) (Z_to_bv 64 (T + 16)) s8 (Z_to_bv 64 4294967295) (Z_to_bv 64 40) s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x4b598) fc None m' (seg_rom rsegs))).
    { intros until m'; intros MU WM MI' KB'.
      assert (R' : rw_cells rsegs m' (T + 16 + 40 * i) [CB 24 hb; C8 (wz Kj); C4 (wz lenj); C4 (wz nxj)]) by (eapply rw_cells_transport; [exact R| exact MU| exact WM| exact I]).
      eapply evt_cut. { eapply (oL_W2 ra' sp gp tp) with (Si := T + 16 + 40 * i); [exact MI'| lia| lia| exact R'| exact NX]. }
      cbv beta. (intros ms1 nd_i1; ndestruct nd_i1 as (pc' & [[NXE ->]|[NXE ->]] & ->)).
      - apply evt_done. unfold walk_post. neexists 18. exists m', 0x4b3a8. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. left. reflexivity.
      - eapply evt_mono.
        { eapply (IH nxj) with (k := k) (kb := kb); [exact MI'| lia| lia| exact K26| exact T0| exact TH| exact KB'| exact LKB| exact LEN| exact K0| exact KHI| eapply slots_ok_transport; [exact SL| exact MU| exact WM]]. }
        cbv beta. unfold walk_post. (intros ms2 nd_i2; ndestruct nd_i2 as (ra2 & u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & w4 & w5 & u3 & u4 & u5 & u6 & m2 & pc2 & -> & MU2 & WM2 & MI2 & CASES)).
        neexists 18. exists m2, pc2. split; [reflexivity|]. split; [eapply munch_trans; [exact MU| exact MU2]|]. split; [eapply wmono_trans; [exact WM| exact WM2]|]. split; [exact MI2| exact CASES]. }
    destruct (Z.eq_dec lenj len) as [EQ|NE].
    - (* [comment removed for export] *)
      subst lenj.
      eapply evt_cut. { eapply (oL_W1_eq ra sp gp tp t0 t1 t2 s0) with (i := i) (leni := len); [exact MI| lia| exact T0| lia| exact R| lia| exact LEN| reflexivity| lia]. }
      intros ms1 ->.
      destruct (memcmp_model_total kbj kb (Z.to_nat len) ltac:(lia) ltac:(lia)) as [vv HMv].
      pose proof (memcmp_model_range _ _ _ _ HMv) as VR.
      eapply evt_cut.
      { eapply (memcmp_spec (Z_to_bv 64 0x4b5c8) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 E) (Z_to_bv 64 Kj) (Z_to_bv 64 K) (Z_to_bv 64 len)) with (ls := kbj) (rs := kb) (v := vv);
          [rewrite unsigned_lit by lia; exact KBJ| rewrite unsigned_lit by lia; exact KB| rewrite unsigned_lit by lia; exact HMv| exact MI]. }
      intros ms2 PM. ndestruct PM as (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & KBJ2 & KB2).
      rewrite !unsigned_lit in KBJ2, KB2 by lia.
      replace (ret_pc (Z_to_bv 64 0x4b5c8)) with (Z_to_bv 64 0x4b5c8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      eapply evt_cut. { eapply oL_W3; [exact MI2| exact VR]. }
      cbv beta. (intros ms3 nd_i3; ndestruct nd_i3 as (pc3 & [[VNE ->]|[V0 ->]] & ->)).
      + (* [comment removed for export] *)
        eapply NEXT; [exact MU2| exact WM2| exact MI2| exact KB2].
      + (* [comment removed for export] *)
        apply evt_done. unfold walk_post. neexists 18. exists m2, 0x4b5cc. split; [reflexivity|]. split; [exact MU2|]. split; [exact WM2|]. split; [exact MI2|].
        right. split; [reflexivity|]. nexists i, hb, Kj, nxj. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
        split; [eapply rw_cells_transport; [exact R| exact MU2| exact WM2| exact I]|]. split; [exact NX|]. split; [lia|]. split; [lia| exact KJR].
    - (* [comment removed for export] *)
      eapply evt_cut. { eapply (oL_W1_ne ra sp gp tp t0 t1 t2 s0) with (i := i) (leni := lenj); [exact MI| lia| exact T0| lia| exact R| lia| exact LEN| exact NE]. }
      cbv beta. (intros ms1 nd_i4; ndestruct nd_i4 as (xa0 & xa1 & ->)).
      eapply NEXT; [apply munch_refl| apply wmono_refl| exact MI| exact KB].
  Qed.
  (* [comment removed for export] *)
  Definition bkcells : ltac2:(zQ "30!hk4!j6!hgf>2bk@1$0$1@1$0$2") := ltac2:(zQ "60!j6!hk4!lh6!hp5!hgf!ho5\2bk@1$1$0@4$2$0$4\1v$0@1$3@1$5^1^1").
  Lemma bkcells_size : ltac2:(zQ "80!j6!hue!hk4!h8!hob!lif!lj6!lk1>2bk@1$2$0@3$4$3@1$7@1$6^1@2$5N4@2$1$0^1").
  Proof. induction bk as [|v bk IH]; cbn; [reflexivity|]. cbn in IH. rewrite IH. lia. Qed.
  Lemma bkcells_app : ltac2:(zQ "60!hk4!j6!lj6!lke!hgf!hob>2l1@1$0$1>2l2@1$0$1@3$5@1$0$4@1$2@3$3$1^2^1@3$3$4@1$2^2@1$2^1").
  Proof. intros. unfold bkcells. apply map_app. Qed.
  Lemma bk_split3 : ltac2:(zQ "d0!j6!lke!hk4!ll3!hje!hue!h8!hv6!hob!lma!ln0!lna!lo1>2bk@1$2$0>1h$6>0@2$9^1@2$5$0^2@3$8@1$2$0^3@3$1$0@3$a$0^2^3@3$1$0@3$4$0@4$b$0^2^3Z@1$7$0@3$c$0@1$3^2^3").
  Proof.
    intros bk h H. rewrite <- (firstn_skipn h bk) at 1. f_equal.
    destruct (skipn h bk) as [|v r] eqn:E. { exfalso. apply (f_equal (@length _)) in E. rewrite length_skipn in E. cbn in E. lia. }
    cbn. f_equal. { rewrite <- (Nat.add_0_r h), <- nth_skipn, E. reflexivity. }
    replace (S h) with (1 + h)%nat by lia. rewrite <- skipn_skipn, E. reflexivity.
  Qed.
  Lemma bk_nth : ltac2:(zQ "h40!j6!sc!hgf!isa!ht6!hj8!hje!hue!hk4!h8!hv6!jic!lma!lna!lj6!hp5!ho5!rc!it6!htf>1m>0@1$5@1$1#k0@1$b@1$5@1$1#8>1A$0>2bk@1$8$0>1h$9>0@4$3$4^4^3@1$e^2>0@2$c^2@2$7$0^3@4$3$4^6@2$h1^5@2$h2+4@1$h3^3@3$6$2@1$f@1$h0@4$d$0^3^4Z@1$a$2").
  Proof.
    intros m A bk h R H. rewrite (bk_split3 bk h H), !bkcells_app in R.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in R as [_ R]. apply (proj1 (rw_cells_app _ _ _ _ _)) in R as [R _].
    rewrite bkcells_size, length_firstn, Nat.min_l in R by lia. cbn [bkcells map] in R.
    replace (A + Z.of_nat (4 * h)) with (A + 4 * Z.of_nat h) in R by lia. exact R.
  Qed.
  (* [comment removed for export] *)
  Lemma bk_upd : ltac2:(zQ "hc1!j6!sc!ht6!it6!htf!hj8!isa!rc!ll3!lke!hje!hue!hk4!hv6!jic!lj6!hgf!loa!h8!lpb!lma!ln0!lo1!hp5!jn0!jn7!jo0!ho5&>0@1$5@1$1#k0@1$e@1$5@1$1#8>1m~0>2m'~0>1W@1$c$h8>1A$0>2bk@1$c$0>1h$h2>1v$0>0@4$6$2^7^4@1$f^3>0@2$h4^3@2$b$0^4>0@3$h9^7^9^8>0@3$ha$2^a^9>0@3$h1^9^8@2$3+4@1$4^6>0@3$h1^a@2$7@2$7^9@2$3+4@1$4^7+4@2$3+4@1$4@2$h3@2$b$0^8@1$8^7>0@4$6$2^c@2$7^a@2$3+4@1$4^8@3$a$h0@1$h7@1$hb^7@1$d$h0@4$6$2^d^b@1$f@3$9$0@3$h5$0^9^a@3$9$0@3$a$0^8@1$d$0@3$h6$0@1$8^9^a").
  Proof.
    intros m m' W A bk h v R H MU WM D1 D2 Rv. rewrite (bk_split3 bk h H), !bkcells_app in R.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in R as [R1 R]. apply (proj1 (rw_cells_app _ _ _ _ _)) in R as [_ R2].
    rewrite !bkcells_app. apply (proj2 (rw_cells_app _ _ _ _ _)). split.
    { eapply rw_cells_transport; [exact R1| exact MU| exact WM|]. rewrite bkcells_size, length_firstn, Nat.min_l by lia.
      replace (Z.of_nat (4 * h)) with (4 * Z.of_nat h) by lia. exact D1. }
    apply (proj2 (rw_cells_app _ _ _ _ _)). rewrite bkcells_size, length_firstn, Nat.min_l by lia.
    rewrite bkcells_size, length_firstn, Nat.min_l in R2 by lia. cbn [bkcells map cells_size csize Nat.add] in R2 |- *.
    replace (A + Z.of_nat (4 * h)) with (A + 4 * Z.of_nat h) in R2 |- * by lia. split; [exact Rv|].
    eapply rw_cells_transport; [exact R2| exact MU| exact WM|]. fold (bkcells (skipn (S h) bk)). rewrite bkcells_size, length_skipn.
    replace (A + 4 * Z.of_nat h + Z.of_nat 4) with (A + 4 * Z.of_nat h + 4) by lia.
    replace (Z.of_nat (4 * (length bk - S h))) with (4 * Z.of_nat (length bk - S h)) by lia. exact D2.
  Qed.
  Lemma bk_upd_length : ltac2:(zQ "c0!j6!hue!lke!h8!ll3!hje!hk4!hv6!hob!lma!ln0!lo1>2bk@1$6$0>1h$3>1v$0>0@2$9^2@2$1$0^3@3$8$3@2$1$0@3$2$0@3$a$0^3^4@3$2$0@3$5$0^2@1$7$0@3$b$0@1$4^3^4@2$1$0^4").
  Proof. intros. rewrite !length_app, length_firstn, length_skipn. cbn. lia. Qed.
  Lemma bk_upd_ok : ltac2:(zQ "a0!j6!lke!lq2!ll3!hje!hk4!h8!hv6!ln0!lo1>1P>0$0P>2bk@1$5$0>1h$6>1v$0>0@3$2$0^4^3>0@1^5^2@3$2$0^6@3$1$0@3$8$0^4^5@3$1$0@3$4$0^3@1$7$0@3$9$0@1$3^4^5").
  Proof.
    intros P bk h v F Pv. apply Forall_app. split; [| apply Forall_app; split; [constructor; [exact Pv| constructor]|]].
    - rewrite <- (firstn_skipn h bk) in F. apply Forall_app in F. tauto.
    - rewrite <- (firstn_skipn (S h) bk) in F. apply Forall_app in F. tauto.
  Qed.
  (* [comment removed for export] *)
  Lemma bkcells_null_bytes : ltac2:(zQ "b0!sc!lqc!hj8!hk4!h8!hob!lif!j6!lj6!lr6!kg0>1n$4@3$5@1$3@1$2@1$0#8@1$9@1$8@3$1$7+vvvvvvvf^1@3$1@1$2@1$0#8@2$a@1$0#8+vf@2$6N4^1").
  Proof.
    induction n as [|n IH]; [reflexivity|]. cbn [repeat bkcells map cells_bytes cbytes]. fold (bkcells (repeat 4294967295 n)). rewrite IH.
    replace (4 * S n)%nat with (S (S (S (S (4 * n)))))%nat by lia. cbn [repeat app].
    assert (E4 : le4 (wz 4294967295) = [Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255]) by (apply (proj1 (Uapi.stat_bytes_eqb_eq _ _)); vm_compute; reflexivity).
    rewrite E4. reflexivity.
  Qed.
  Lemma bk_of_memset : ltac2:(zQ "f0!sc!hj8!lif!lqc!j6!hgf!isa!ht6!hje!h8!hv6!jic!lj6!ik4!kg0>1m>0@1$1@1$0#k0@1$b@1$1@1$0#8>1A$4>1n$9>0@4$6$7^3^2@3$8$5@2$d@2$2N4^1@3$3@1$1@1$0#8@2$e@1$0#8+vf@2$2N4^1@1$a$5@4$6$7^4^3@1$c@3$3$4+vvvvvvvf^2").
  Proof.
    intros m A n R. eapply rw_cells_rebytes; [exact R| | cbn [cells_bytes cbytes app]; rewrite app_nil_r; apply bkcells_null_bytes| cbn [cells_size csize]; rewrite bkcells_size, repeat_length; lia].
    unfold bkcells. clear R. induction n; cbn; [exact I| split; [exact I| exact IHn]].
  Qed.
  (* [comment removed for export] *)
  Definition probe_post : ltac2:(zQ "80!sc!hj8!j6!h8!hk4!js0!jv7!o4>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s6@1$1@1$0#k0>2s8@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1T$2>3len$2>1n$3>1k$3>2bk@1$4$2>1m$7>0$5P") := ltac2:(zQ "i81!sc!hj8!s7!pe!j6!rc!kg0!hob!hgf!s2!hje!h8!ht6!it6!hk4!ho5!hh6!htf!hv6!jic!hp0!js0!hp5!kgb!lma!lna!jv7!ij6!ijf!ik4!jn0!kh1!jn7!jo0!kl5!klb!kq5!isa!o4!hu8&>0@1$1@1$0#k0@1$h3@1$1@1$0#8\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s6@1$1@1$0#k0\2s8@1$1@1$0#k0\1F@2$ha@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1T$4\3len$4\1n$b\1k$b\2bk@1$e$4\1m$i6\2ms$h5@2$2@1$1@1$0#k0\3ra'@1$1@1$0#k0@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2s4@1$1@1$0#k0@2$2@1$1@1$0#k0\2s5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2$4\3pc'$4@2$2$b\1h$b@2$3@2$h8^1^ha@2$3@3$7$h5^h6@7$i2@hf$hf^h5^i6^i5^i4^h4^h3^h2@2$6@1$0#k0@2$5@2$5@2$5^hc+h0@2$d@1$h1^ha+i8@2$d+4@1$h1^1^i3^h1^h0^f^e^d^c^b^a^i2^i1^9^8^i0@2$6@1$0#k0@2$5^hc+h0^hf@2$6@1$0#k0+vvvvvvvf@2$6@1$0#k0+i8@2$6@1$0#k0@4$h9$4^1^h8Z^7^6^5^4^he@2$6@1$0#k0^2^hd@1$h7@1$1@1$0#k0^3@1$i4$c@2$3@3$i0@1$h2$he^h7^3@2$3@3$i1$c^h7^3@2$3@2$i3$c^3@2$h4@3$7$4^2+krjq8@2$3@3$7$4^2+krlsc@2$2$4\1j$4@2$2@1$e@1$1@1$0#8\2hb@1$e@1$1@1$0#8@2$2$4\2Kj$4@2$2$4\3nxj$4@2$3@2$3@2$9Z^4@2$h0^4@1$h1^hd@2$3@3$7@1$1@1$0#k0^d@2$6@1$0#k0@2$5@2$5^i0+h0@2$d+i8^4@2$3@3$7@1$1@1$0#k0^c@2$6@1$0#k0^2@2$3@4$i5$c^7@2$5@2$5^i0+h0@2$d+i8^4@3$a$8@2$hdNh8^3@3$a$8@1$hc@1$f^2@3$a$8@1$h6@1$f^hf@3$a$8@1$h6@1$f^1@1$h2$8@2$3@2$3@2$9Z^1@2$h0^1@2$i7+2+i0@2$3@2$h0Z^2@2$3@2$9@2$5^2@2$5^hf+1@1$hb?5HCEIL@2$h4@2$9@2$5^2@2$5^hf+1+hggg0@2$9+hitgg0^2").

  Lemma oL_probe : ltac2:(zQ "ib0!sc!hj8!kg0!j6!ht6!rc!htf!s2!hob!hgf!hh6!hje!hk4!h8!isa!hu8!hue!pe!ls4!mg8!it6!kgb!hv6!hp0!lq2!jv7!mh4!lj6!mi3!ji0!ij6!hp5!ijf!ik4!kv8!kh1!kl5!io3!klb!kq5!o4!mj1!mk0>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s7@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h9@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$i8>1T$3>1K$3>3len$3>1E$3>1S$3>2SP$3>4endp$3>3dst$3>1n$d>1k$d>2kb@1$c@1$1@1$0#8>2j0@1$c@1$1@1$0#8>2bk@1$c$3>0@2$i6$4^e>0@3$8@1$1@1$0#k0^i6@2$2@1$0#k0^9>0@4$e$4^h0^a@2$ha^9^8>0@2$7Z^b>0@2$7@2$5^c+j8@2$f+2+k0>0@2$h1@2$7Z^h0@2$a^h0@2$f+2+hf>0@2$aZ^h2>0@2$7@2$5^h3@2$5^h2+1@1$he?5HCEIL>0@4$i5$4^h6^h4^b>0@3$8$3@1$6@2$h0@1$1@1$0#8^c@2$5^h4+1>0@2$h2N1^f>0@2$a@1$6^h0@2$f+2+h9>0@2$h2^h0^h1>0@4$e$4^hb^ha@3$b$9@2$i1N4^f@3$b$9@1$hf@2$2@1$0#k0@1$6^h2@3$b$9@1$i0@2$2@1$0#k0^ha@1$h6$9>0@3$i9?5HCEIL^hb@2$5@2$h4@1$6^h3+ic+h0>0@4$e$4^hd@2$5@2$5^hc+h0@2$h4@1$6^h4+i8@1$hb^h0>0@3$8$d@2$h0$3^h1^h5>0@3$h8$3\1v$3@2$h7@3$8$3^1+vvvvvvvf@2$h1@2$7Z^1@2$a^1@1$6^h6^h2>0@3$hd^i0^hf^h6@3$i2$4@h0$hc^j8^j7^j6@2$2@1$0#k0^hd@2$2@1$0#k0^hf@2$2@1$0#k0^he@2$2@1$0#k0^hc@2$2@1$0#k0$h3^i3^i2^i0^he^h8^h7^h4^i1@7$i4@hf$i3^j9^j8^j7^j6^j5^j4^j3^j2@2$2@1$0#k0^hd@2$2@1$0#k0^i0^j1^j0@2$2@1$0#k0@2$ia^he+vvvvvvv8^if^ie^id^ic@2$2@1$0#k0^hf@2$2@1$0#k0^he^ib^ia@2$2@1$0#k0^hc^i9@2$2@1$0#k0$h3@2$2@1$0#k0+vvvvvvvf@2$2@1$0#k0+i8^i8^i7^i6^i5^i4^i3@2$2@1$0#k0+krkl8^i2@1$h5@1$1@1$0#k0^i1@1$i7$4").
  Proof.
    intros until bk; intros MI ESP FRS SP0 SPH LEN K0 KH KB LKB N1 N25 KN TB TR BK LBK BOK SL.
    npose TR as (TR1 & TR2 & TR3 & TR4 & TR5). hcb.
    pose proof (Z.div_pos len 8 ltac:(lia) ltac:(lia)) as D0. assert (D2 : 8 * (len / 8) <= len) by (pose proof (Z.mul_div_le len 8 ltac:(lia)); lia).
    pose proof (Z.mod_pos_bound len 8 ltac:(lia)) as M8. pose proof (Z.div_mod len 8 ltac:(lia)) as DM.
    (* [comment removed for export] *)
    assert (TO558 : evt rsegs (fun ms => exists (xa1 xa4 xa5 xa6 xa7 xt0 xt1 xt2 : word),
              ms = MS (mkR ra sp gp tp xt0 xt1 xt2 s0 (Z_to_bv 64 E) (Z_to_bv 64 T) xa1 (Z_to_bv 64 (K + 8 * (len / 8))) (Z_to_bv 64 0) xa4 xa5 xa6 xa7 (Z_to_bv 64 K) (Z_to_bv 64 len) s4 s5 (Z_to_bv 64 S) s7 (Z_to_bv 64 OCL_KMUL) (Z_to_bv 64 4294967295) (Z_to_bv 64 40) s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x4b4e8) fc None m (seg_rom rsegs))
              (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 E) (Z_to_bv 64 T) a1 a2 (Z_to_bv 64 (Z.land len 4294967288)) a4 a5 a6 a7 (Z_to_bv 64 K) (Z_to_bv 64 len) s4 s5 (Z_to_bv 64 S) s7 (Z_to_bv 64 OCL_KMUL) (Z_to_bv 64 4294967295) (Z_to_bv 64 40) s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x4b458) fc None m (seg_rom rsegs))).
    { eapply evt_cut. { eapply oL_D0; [exact MI| exact LEN| exact K0| lia]. }
      cbv beta. (intros ms1 nd_i5; ndestruct nd_i5 as (pc1 & xa2 & xa4 & [(Z0 & -> & -> & ->)|(ZP & -> & -> & ->)] & ->)).
      - apply evt_done. rewrite Z0. replace (K + 8 * 0) with K by lia. change (8 * 0) with 0. neexists 8. reflexivity.
      - eapply evt_mono.
        { eapply (oL_DW (Z.to_nat (len / 8))) with (K := K) (kb := kb); [exact MI| exact KB| lia| lia| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia]. }
        cbv beta. (intros ms2 nd_i6; ndestruct nd_i6 as (xa1 & xa5 & xa6 & xa7 & xt0 & xt1 & xt2 & ->)). rewrite unsigned_lit by lia.
        replace (K + 8 * Z.of_nat (Z.to_nat (len / 8))) with (K + 8 * (len / 8)) by lia. neexists 8. reflexivity. }
    eapply evt_cut; [exact TO558|]. cbv beta. (intros ms1 nd_i7; ndestruct nd_i7 as (xa1 & xa4 & xa5 & xa6 & xa7 & xt0 & xt1 & xt2 & ->)). clear TO558.
    (* [comment removed for export] *)
    eapply evt_cut. { eapply oL_DJ with (len := len); [exact MI| exact ESP| reflexivity| lia| exact FRS| exact SP0| exact SPH]. }
    cbv beta. (intros ms2 nd_i8; ndestruct nd_i8 as (t & Ht & ->)).
    eapply evt_cut. { eapply (oL_DT t) with (K := K) (kb := kb); [exact MI| exact KB| lia| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia]. }
    cbv beta. (intros ms3 nd_i9; ndestruct nd_i9 as (ya1 & ya2 & ya3 & ->)).
    (* [comment removed for export] *)
    eapply evt_cut. { eapply oL_H1 with (n := n); [exact MI| exact N1| lia| exact TB| exact TR]. }
    cbv beta. (intros ms4 nd_i10; ndestruct nd_i10 as (h' & za0 & za1 & za2 & Hh & ->)).
    pose proof (bk_nth m _ bk (Z.to_nat h') BK ltac:(lia)) as BKH. rewrite Z2Nat.id in BKH by lia.
    pose proof (proj1 (Forall_forall _ _) BOK _ (@nth_In _ (Z.to_nat h') bk 0 ltac:(lia))) as VOK. cbv beta in VOK.
    eapply evt_cut.
    { eapply oL_H2 with (BK := T + 16 + Z.of_nat n * 40 + 4 * h') (v := nth (Z.to_nat h') bk 0); [exact MI| reflexivity| lia| lia| exact BKH| lia]. }
    cbv beta. (intros ms5 nd_i11; ndestruct nd_i11 as (pc5 & [[VN ->]|[VN ->]] & ->)).
    - (* [comment removed for export] *)
      apply evt_done. unfold probe_post. neexists 18. nexists m, 0x4b3a8, (Z.to_nat h'). split; [lia|]. rewrite Z2Nat.id by lia.
      split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. left. reflexivity.
    - (* [comment removed for export] *)
      eapply evt_mono.
      { eapply (oL_walk (Datatypes.S (Z.to_nat (nth (Z.to_nat h') bk 0)))) with (k := k) (kb := kb); [exact MI| lia| lia| lia| lia| lia| exact KB| lia| exact LEN| lia| lia| exact SL]. }
      cbv beta. unfold walk_post, probe_post. (intros ms6 nd_i12; ndestruct nd_i12 as (ra2 & u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & w4 & w5 & u3 & u4 & u5 & u6 & m2 & pc2 & -> & MU2 & WM2 & MI2 & CASES)).
      neexists 18. nexists m2, pc2, (Z.to_nat h'). split; [lia|]. rewrite Z2Nat.id by lia.
      split; [reflexivity|]. split; [exact MU2|]. split; [exact WM2|]. split; [exact MI2| exact CASES].
  Qed.
End HCW2.
