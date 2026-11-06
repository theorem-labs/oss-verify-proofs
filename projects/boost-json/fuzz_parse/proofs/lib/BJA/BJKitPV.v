(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep CellsX TacX Bytes Mem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep CXXLib AsObj.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJA Require Import BJRep AXpres BJIface BJKitVS BJKitPA.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14list37Corelib5Lists7ListDefm03map01Z37Corelib4Init5Logico02eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~p92b8hfbbv_unsignedo03andm06Forall46Stdlib6ZArith6BinInt1Zv62lev62ltv63addk16lengtho02ex79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~hic5asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsIface~~~~~~hn05blockhn03mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~hrdaaccessiblehrdain_app_memhrd5shvis79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJA7BJIface~~~~~~ii08input_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ima8bytes_atv66of_nat36Stdlib5Lists4Listir92Inhn08as_RHEAPhn05as_Sthrd5aceilo02orhn06as_RFShn06fframe79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJA6AXpres~~~~~~jg97inframe79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~jl14cell79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~jp58rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJA7BJKitPA~~~~~~jtccparser_cellsk14consk13natk13nilk16option79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJA5BJRep~~~~~~kk66pstatejl12CBjl1acells_sizek14boolk15falsekk68ps_depthkk68ps_ecsetkk66ps_endkk67ps_moreo03iffk14prodhrdbaddressablehrd2shk13fstk13sndhrd3nsh79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As6CXXRep~~~~~~lh15xpreshn03asrhn0casan_rt_hyps" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma map_b8_unsigned : ltac2:(zQ "80!h9!jc!l9!n7!nd!p4!t4!t9>2bs@1$2@1$1@1$0#8@3$5@1$2@1$1@1$0#8@4$3$4@1$1@1$0#8$6@4$3@1$1@1$0#8$4\1b@1$1@1$0#8@2$7@1$0#8^1^1^1").
Proof. induction bs as [|b bs IH]; [reflexivity|]. cbn [map]. rewrite IH. unfold b8. rewrite definitions.Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma Forall_unsigned_byte : ltac2:(zQ "a0!h9!nd!jc!l9!u7!ud!n7!hge!hh3!t9>2bs@1$3@1$2@1$0#8@3$5$1\1c$1@2$4@2$7Z^1@2$8^1+hg0@4$6@1$2@1$0#8$1\1b@1$2@1$0#8@2$9@1$0#8^1^1").
Proof.
  induction bs as [|b bs IH]; [constructor|]. cbn [map]. constructor; [| exact IH].
  pose proof (bv_unsigned_in_range _ b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.

Section K.
  Context {HCEIL : HeapCeil}.
  Variable H : ltac2:(zQ "10!ll6$0").
  Hypothesis RT : ltac2:(zQ "10!lld@2$0?5HCEIL?1H").

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma input_sub : ltac2:(zQ "h70!nd!u7!hh8!l9!hge!h9!hh3!jc!hhe!p4!hi7!ud!n7!hm7!hqd!hr6!hvb!ig9!ih7!ile!iq4!t4!ir0>4REST@1$3$e>2sp@1$7@1$5#k0>1m$f>2p0$0>3len$0>1A$0>1n$0>0@5$h3^7^6^5^4^3>0@2$4^5^3>0@2$6Z^3>0@2$4@2$2^5^4@2$2^7^6@2$a@1$3$0\2lz@1$3$0@2$1@3$9$0@1$h6@2$8$0^1^6@2$1@4$h4$d^a^7@4$c$0@1$7@1$5#8$h5^1@2$1@3$b$0\1c$0@2$1@2$4Z^1@2$6^1+hg0^1@2$1@3$h0^a^7^6@2$1@3$h2^a^7@2$2^7^6@2$h1^7@2$2^7^6").
  Proof.
    (intros REST sp m p0 len A n nd_i1 H1 H2 H3; ndestruct nd_i1 as ((ibs & ILEN & IBY) & _ & IP0 & IP47 & IACC & ISHV & IAPP & _)).
    set (i := Z.to_nat (A - p0)). set (bs := firstn (Z.to_nat n) (skipn i ibs)).
    exists (map (fun b : byte => bv_unsigned b) bs).
    assert (LB : length bs = Z.to_nat n). { subst bs i. rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn. lia. }
    split. { rewrite length_map, LB. lia. }
    split. { rewrite map_b8_unsigned. replace A with (p0 + Z.of_nat i) by (subst i; lia). subst bs. apply bytes_at_sub; [exact IBY| subst i; lia]. }
    split; [apply Forall_unsigned_byte|].
    split; [eapply accessible_sub; [exact IACC| lia| lia| lia]|].
    split; [eapply shvis_sub; [exact ISHV| lia| lia| lia| lia| lia]|].
    eapply in_app_mem_sub; [exact IAPP| lia| lia].
  Qed.

  Lemma input_end_le_aceil : ltac2:(zQ "e0!hqd!l9!nd!hr6!isc!h9!it2!ite!iu7!ile!hh8!hge!hh3!jc>1s@1$7?1H>2LB@1$1$0>4REST@1$1$0>2sp@1$d@1$5#k0>1m$3>2m'$3>2p0$2>3len$2>0@5$9^6^5^4^2^1>0@4$6?1H^9^8^4>0>1b$0>0@3$4$0^1^9@3$4$0^2^b>0@2$cZ^4@2$b@2$a^6^5@1$8?5HCEIL").
  Proof.
    (intros s LB REST sp m m' p0 len nd_i2 RH SUB Hl; ndestruct nd_i2 as (_ & IBLK & _)).
    destruct IBLK as [L0 | (b & Hb & B1 & B2)]; [lia|].
    pose proof (ablock_facts H _ _ (ah_blocks H RT _ _ _ b RH (SUB b Hb))) as (_ & _ & _ & _ & R5 & _). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma input_frame_apart : ltac2:(zQ "h10!hqd!nd!hh8!l9!hr6!isc!hge!iv0!h9!iv5!it2!ite!ivf!jk6!ile!hh3!jc>1s@1$b?1H>2LB@1$3$0>4REST@1$3$0>2sp@1$h0@1$8#k0>1m$4>2m'$4>2LF@1$3$c>2m1$4>2p0$1>3len$1>1A$1>1n$1>0@5$e^a^9^8^4^3>0@4$a?1H^d^c^8>0>1b$0>0@3$5$0^1^d@3$5$0^2^f>0@3$9?1H^9^8>0@3$d^a^6^5>0@2$fZ^8@2$7@2$6@2$2@2$2^8^7+h0^a@2$6@2$2@2$2^a^9+h0^8").
  Proof.
    (intros s LB REST sp m m' LF m1 p0 len A n nd_i3 RH SUB RF IFR Hl; ndestruct nd_i3 as (_ & IBLK & _)).
    destruct IBLK as [L0 | (b & Hb & B1 & B2)]; [lia|].
    pose proof (inframe_block_disjoint H RT _ _ _ _ _ _ _ b RH RF IFR (SUB b Hb)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma parser_cells_relit : ltac2:(zQ "h50!h9!hh8!jc!hm7!jod!jt0!l9!nd!kha!hge!kia!hhe!kj1!kj7!kjd!p4!hr6!ko2!koc!kp2!ir0>1m$h0>2m'>0@1$2@1$0#k0@1$e@1$2@1$0#8>1a$7>2ps$h1>2j8@1$6@1$2@1$0#8>0@3$8^5^3^2>0>1A$7>2cs@1$6$4>0@4$5$3^8^2^1>0@2$9@2$1^7+k0^3>0@2$9@2$1^4@1$h4@1$h3^3@2$1^8+hh0@4$5$3^a^5^4>0@3$f$c@2$b@1$2@1$0#8^3N8>0@4$5$3^7@2$1^6+hh0@3$a$4@2$h2N8^4@1$d$4@3$8^8^7^6").
  Proof.
    (intros m m' a ps j8 nd_i4 TR LJ RJ; ndestruct nd_i4 as (NUM & ECC & STZ & SCR & MOREC & ENDC & NB & NBP & OPT & DEPC & LITC)).
    assert (T : forall A cs, rw_cells asegs m A cs -> a + 64 <= A -> A + Z.of_nat (cells_size cs) <= a + 272 -> rw_cells asegs m' A cs) by exact TR.
    split. { ndestruct NUM as (num & Ln & Rn). exists num. split; [exact Ln|]. apply T; [exact Rn| lia| cbn; lia]. }
    split. { ndestruct ECC as (e1 & e2 & e3 & Re & Hiff & Hne1). nexists e1, e2, e3. split; [| split; [exact Hiff| exact Hne1]]. apply T; [exact Re| lia| cbn; lia]. }
    split. { apply T; [exact STZ| lia| cbn; lia]. }
    split. { ndestruct SCR as (sc & Ls & Rs). exists sc. split; [exact Ls|]. apply T; [exact Rs| lia| cbn; lia]. }
    split. { ndestruct MOREC as (dn & cl & p5 & Lp & Rm). nexists dn, cl, p5. split; [exact Lp|]. apply T; [exact Rm| lia| cbn; lia]. }
    split. { apply T; [exact ENDC| lia| cbn; lia]. }
    split. { ndestruct NB as (nb & Lb & Rb). exists nb. split; [exact Lb|]. apply T; [exact Rb| lia| cbn; lia]. }
    split. { apply T; [exact NBP| lia| cbn; lia]. }
    split. { destruct OPT as (pd2 & Ro). exists pd2. apply T; [exact Ro| lia| cbn; lia]. }
    split. { apply T; [exact DEPC| lia| cbn; lia]. }
    exists j8. split; [exact LJ| exact RJ].
  Qed.

  (* [comment removed for export] *)
  Lemma parser_cells_ecset : ltac2:(zQ "c0!p4!kq0!nd!kq7!kha!kqf!krb!ks7!kt1!ko2!ktc!hr6>1m$b>1a$2>2ps$9>3ps'$9>0@3$4^4^3^2>0@3$0$2@1$7^2@1$7^3>0@3$0$2@1$5^3@1$5^4>0@3$0$1@1$8^4@1$8^5>0@2$a@3$0$1@1$6^5$3@3$0$1@1$6^6$3@3$4^9^8^6").
  Proof.
    (intros m a ps ps' nd_i5 E1 E2 E3 E4; ndestruct nd_i5 as (NUM & ECC & STZ & SCR & MOREC & ENDC & NB & NBP & OPT & DEPC & LITC)).
    split; [exact NUM|]. split. { ndestruct ECC as (e1 & e2 & e3 & Re & Hiff & Hne1). nexists e1, e2, e3. split; [exact Re|]. split; [| exact Hne1]. tauto. }
    split; [exact STZ|]. split; [exact SCR|]. split; [rewrite E3; exact MOREC|]. split; [rewrite E1; exact ENDC|].
    split; [exact NB|]. split; [exact NBP|]. split; [exact OPT|]. split; [rewrite E2; exact DEPC| exact LITC].
  Qed.

  Lemma inframe_xpres_addressable : ltac2:(zQ "h20!nd!l9!ku2!hr6!hge!ku9!kv8!kve!lg4!iv0!ud!iv5!hqd!ivf!lga!lkd!jk6!hh8>2LF@1$1$d>2m1$3>2LB@1$1$c>2SP$0>1X@1$1@2$2$0$0>1m$3>2m'$3>1A$0>1n$0>0@3$b?1H^9^8>0@3$h0^a^3^2>0@2$4Z^3>0@7$f?5HCEIL?1H^a^9^8^7^6>0@3$5^8^6^5>0@3$a@2$2$0$0\2iv@2$2$0$0@2$9@2$4@2$h1@1$6^8@1$e^7@3$7$0$0^1@2$4@3$8$0$0^1@1$6^8^a@3$5^9^8^7").
  Proof.
    (intros LF m1 LB SP X m m' A n RF nd_i6 Hn XP AD FX; ndestruct nd_i6 as (f & Hf & H1 & H2)).
    eapply xpres_addressable; [exact XP| exact AD|]. split; [| exact FX].
    pose proof (proj2 (ah_RFS_range H RT _ _ RF) f Hf) as (K & R1 & R2 & R3 & R4); pose proof (proj1 (ah_RFS_range H RT _ _ RF)) as (F1 & F2 & F3).
    right; right; right; right; right; left. unfold AFS_HDR in *.
    split; [apply sh_mono; lia|]. unfold AFS_SIZE, sh, nsh in *. Z.div_mod_to_equations. lia.
  Qed.
End K.
