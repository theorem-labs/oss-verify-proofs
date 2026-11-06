(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep TacX ZBridge Exec CellsX Bytes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJU Require Import BJRep BJKitVS.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~hf4cell35stdpp9bitvectorbdefinitionsm22bv46Stdlib6ZArith6BinInt1Zo46to_nat37Corelib4Init9Datatypesq54consq53nilhf2CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~sf8rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~hh55rsegso43add37Corelib5Lists7ListDefhm15skipno46of_natq53nat37Corelib4Init5Logichp03and37Corelib4Init3Nathqb3subhm16firstn01Zo42leq54listq56optionhp02exhf2C1hqb3addhfacells_sizehp02eq" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section K.
  Context {HCEIL : HeapCeil}.

  (* [comment removed for export] *)
  Lemma buf_open : ltac2:(zQ "h40!h9!lb!nf!pc!rd!s4!sa!hga!hl2!hlb!hn8!ho1!hoa!hq4!hrd!hs4!hse!ht1!ht6!htd>1m>0@1$2@1$0#k0@1$h3@1$2@1$0#8>1A$h0>1n$c>3buf@1$h2@1$2@1$0#8>1i$h0>1k$c>0@4$7$8^6^5@3$4$1@2$6^4^3@1$5$1>0@2$h1Z^3>0@2$h1@2$9^4@1$b^3@1$b^6@2$d@4$7$8^9^8@3$4$1@2$6@1$3^5@3$f@1$2@1$0#8@1$3^5^6@1$5$1@2$d@4$7$8^9@2$9^8^5@3$4$1@2$6^4@3$f@1$2@1$0#8^4@3$a@1$2@1$0#8@1$3^5^6@1$5$1@4$7$8^9@2$9@2$9^8^5@1$b^4@3$4$1@2$6@2$e@2$e^7@1$3^5^4@3$a@1$2@1$0#8^4@3$a@1$2@1$0#8@1$3^5^6@1$5$1").
  Proof.
    intros m A n buf i k H Hi Hk.
    destruct (rw_cells_CB_split rsegs m A n (Z.to_nat i) buf H ltac:(lia)) as [H1 H2].
    replace (A + Z.of_nat (Z.to_nat i)) with (A + i) in H2 by lia.
    destruct (rw_cells_CB_split rsegs m (A + i) (n - Z.to_nat i) k (skipn (Z.to_nat i) buf) H2 ltac:(lia)) as [H3 H4].
    split; [exact H1|]. split; [exact H3| exact H4].
  Qed.

  Lemma CB1_cells : ltac2:(zQ "d0!h9!nf!lb!rd!s4!hga!hl2!ht6!htd!hu6!hse!huc!sa>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>1A$a>1l@1$7@1$1@1$0#8>0@4$5$6^3^2@3$3$2@2$cN1^1@1$4$2@2$9@1$1@1$0#8\2b0@1$1@1$0#8@4$5$6^5^4@3$3$2@1$b^1@1$4$2").
  Proof.
    intros m A l H. pose proof H as [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as [L _].
    destruct l as [|b0 [|? ?]]; cbn in L; try lia. exists b0.
    split; [split|]; [cbn; tauto | cbn [cells_bytes cbytes app] in *; exact Hb | cbn [cells_size csize Nat.add] in *; exact Hw].
  Qed.

  Lemma CB4_cells : ltac2:(zQ "d0!h9!nf!lb!rd!hu6!huc!s4!hga!hl2!ht6!htd!hse!sa>1m>0@1$1@1$0#k0@1$a@1$1@1$0#8>1A$b>1l@1$9@1$1@1$0#8>0@4$7$8^3^2@3$3$2@2$cN4^1@1$6$2@2$4@1$1@1$0#8\2b0@1$1@1$0#8@2$4@1$1@1$0#8\2b1@1$1@1$0#8@2$4@1$1@1$0#8\2b2@1$1@1$0#8@2$4@1$1@1$0#8\2b3@1$1@1$0#8@4$7$8^8^7@3$3$2@1$5^4@3$3$2@1$5^3@3$3$2@1$5^2@3$3$2@1$5^1@1$6$2").
  Proof.
    intros m A l H. pose proof H as [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as [L _].
    destruct l as [|b0 [|b1 [|b2 [|b3 [|? ?]]]]]; cbn in L; try lia. nexists b0, b1, b2, b3.
    split; [split|]; [cbn; tauto | cbn [cells_bytes cbytes app] in *; exact Hb | cbn [cells_size csize Nat.add] in *; exact Hw].
  Qed.

  (* [comment removed for export] *)
  Lemma buf_close : ltac2:(zQ "h20!lb!h9!nf!ht6!hoa!hga!hl2!rd!s4!sa!hlb!ho1!hv1!hv8!htd!ig5!hu6!hse>1m>0@1$2@1$1#k0@1$e@1$2@1$1#8>1A$h1>1i$4>3pre@1$3@1$2@1$1#8>2cs@1$3$0>1j$4>4post@1$3@1$2@1$1#8>1n$4>0@4$5$6^8^7@3$7$0@2$9^6^5@1$8$0>0@4$5$6^9@2$a^8@1$b^7^5>0@4$5$6^a@2$a@2$a^9@1$b^8@1$b@1$d^6@3$7$0@2$9^5^4@1$8$0>0@3$f$4@2$c@2$c^9@1$d^7^6^4@2$h0@1$3@1$2@1$1#8\4buf'@1$3@1$2@1$1#8@4$5$6^d^c@3$7$0@2$9^6^1@1$8$0").
  Proof.
    intros m A i pre cs j post n H1 H2 H3 Hn.
    pose proof (rw_cells_as_CB _ _ _ H2) as H2'.
    pose proof (rw_cells_CB_join rsegs m A i (cells_size cs) pre (cells_bytes cs) H1 H2') as H12.
    pose proof (rw_cells_CB_join rsegs m A (i + cells_size cs) j (pre ++ cells_bytes cs) post H12) as H123.
    replace (A + Z.of_nat (i + cells_size cs)) with (A + Z.of_nat i + Z.of_nat (cells_size cs)) in H123 by lia.
    specialize (H123 H3). rewrite Hn in H123. eexists. exact H123.
  Qed.

  (* [comment removed for export] *)
  Lemma buf_open4 : ltac2:(zQ "h20!h9!nf!lb!rd!hu6!ht6!s4!huc!hga!hl2!hlb!sa!hq4!hrd!hse!ht1!pc!htd>1m>0@1$1@1$0#k0@1$h1@1$1@1$0#8>1A$e>3buf@1$5@1$1@1$0#8>2sz$e>0@4$8$9^4^3@3$3$2@2$bNhg0^2@1$6$2>0@2$fZ^2>0@2$f@2$a^3+4+hg0@2$4@1$5@1$1@1$0#8\3pre@1$5@1$1@1$0#8@2$4@1$1@1$0#8\2b0@1$1@1$0#8@2$4@1$1@1$0#8\2b1@1$1@1$0#8@2$4@1$1@1$0#8\2b2@1$1@1$0#8@2$4@1$1@1$0#8\2b3@1$1@1$0#8@2$4@1$5@1$1@1$0#8\4post@1$5@1$1@1$0#8@2$c@4$8$9^d^c@3$3$2@2$b@1$h0^a^6@1$6$2@2$c@4$8$9^d@2$a^c^a@3$3$2@1$7^5@3$3$2@1$7^4@3$3$2@1$7^3@3$3$2@1$7^2@1$6$2@4$8$9^d@2$a@2$a^c^a+4@3$3$2@2$b@2$d@2$dNhg0@1$h0^aN4^1@1$6$2").
  Proof.
    intros m A buf sz H Hs Hr.
    ndestruct (buf_open m A 256 buf sz 4 H Hs ltac:(cbn; lia)) as (H1 & H2 & H3).
    destruct (CB4_cells _ _ _ H2) as (b0 & b1 & b2 & b3 & H2').
    nexists (firstn (Z.to_nat sz) buf), b0, b1, b2, b3, (skipn 4 (skipn (Z.to_nat sz) buf)).
    split; [exact H1|]. split; [exact H2'|]. exact H3.
  Qed.
  Lemma buf_open1 : ltac2:(zQ "h20!h9!nf!lb!ht6!rd!s4!hga!hl2!hlb!hu6!sa!hq4!hrd!hse!ht1!pc!htd!huc>1m>0@1$1@1$0#k0@1$h0@1$1@1$0#8>1A$d>3buf@1$3@1$1@1$0#8>2sz$d>0@4$6$7^4^3@3$4$2@2$aNhg0^2@1$5$2>0@2$eZ^2>0@2$e@2$8^3+1+hg0@2$9@1$3@1$1@1$0#8\3pre@1$3@1$1@1$0#8@2$9@1$1@1$0#8\2b0@1$1@1$0#8@2$9@1$3@1$1@1$0#8\4post@1$3@1$1@1$0#8@2$b@4$6$7^a^9@3$4$2@2$a@1$f^7^3@1$5$2@2$b@4$6$7^a@2$8^9^7@3$4$2@1$h1^2@1$5$2@4$6$7^a@2$8@2$8^9^7+1@3$4$2@2$a@2$c@2$cNhg0@1$f^7N1^1@1$5$2").
  Proof.
    intros m A buf sz H Hs Hr.
    ndestruct (buf_open m A 256 buf sz 1 H Hs ltac:(cbn; lia)) as (H1 & H2 & H3).
    destruct (CB1_cells _ _ _ H2) as (b0 & H2').
    nexists (firstn (Z.to_nat sz) buf), b0, (skipn 1 (skipn (Z.to_nat sz) buf)).
    split; [exact H1|]. split; [exact H2'|]. exact H3.
  Qed.
  Lemma buf_close4 : ltac2:(zQ "h10!lb!h9!nf!rd!ht6!s4!huc!hga!hl2!hlb!sa!hrd!hse!ht1!pc!htd!hu6>1m>0@1$2@1$1#k0@1$f@1$2@1$1#8>1A$c>2sz$c>3pre@1$4@1$2@1$1#8>2b0@1$2@1$1#8>2b1@1$2@1$1#8>2b2@1$2@1$1#8>2b3@1$2@1$1#8>4post@1$4@1$2@1$1#8>0@2$dZ^7>0@2$d@2$9^8+4+hg0>0@4$7$8^b^a@3$3$0@2$a@1$e^9^8@1$5$0>0@4$7$8^c@2$9^b^a@3$3$0@1$6^8@3$3$0@1$6^7@3$3$0@1$6^6@3$3$0@1$6^5@1$5$0>0@4$7$8^d@2$9@2$9^c^b+4@3$3$0@2$a@2$b@2$bNhg0@1$e^bN4^5@1$5$0@2$h0@1$4@1$2@1$1#8\4buf'@1$4@1$2@1$1#8@4$7$8^f^e@3$3$0@2$aNhg0^1@1$5$0").
  Proof.
    intros m A sz pre b0 b1 b2 b3 post Hs Hr H1 H2 H3.
    eapply (buf_close m A (Z.to_nat sz) pre [C1 b0; C1 b1; C1 b2; C1 b3] (256 - Z.to_nat sz - 4) post 256).
    - exact H1.
    - replace (A + Z.of_nat (Z.to_nat sz)) with (A + sz) by lia. exact H2.
    - cbn [cells_size csize Nat.add]. replace (A + Z.of_nat (Z.to_nat sz) + 4) with (A + sz + 4) by lia. exact H3.
    - cbn [cells_size csize Nat.add]. lia.
  Qed.
  Lemma buf_close1 : ltac2:(zQ "h10!lb!h9!nf!rd!ht6!s4!hga!hl2!hlb!sa!hrd!hse!ht1!pc!htd!hu6!huc>1m>0@1$2@1$1#k0@1$e@1$2@1$1#8>1A$b>2sz$b>3pre@1$4@1$2@1$1#8>2b0@1$2@1$1#8>4post@1$4@1$2@1$1#8>0@2$cZ^4>0@2$c@2$8^5+1+hg0>0@4$6$7^8^7@3$3$0@2$9@1$d^6^5@1$5$0>0@4$6$7^9@2$8^8^7@3$3$0@1$h0^5@1$5$0>0@4$6$7^a@2$8@2$8^9^8+1@3$3$0@2$9@2$a@2$aNhg0@1$d^8N1^5@1$5$0@2$f@1$4@1$2@1$1#8\4buf'@1$4@1$2@1$1#8@4$6$7^c^b@3$3$0@2$9Nhg0^1@1$5$0").
  Proof.
    intros m A sz pre b0 post Hs Hr H1 H2 H3.
    eapply (buf_close m A (Z.to_nat sz) pre [C1 b0] (256 - Z.to_nat sz - 1) post 256).
    - exact H1.
    - replace (A + Z.of_nat (Z.to_nat sz)) with (A + sz) by lia. exact H2.
    - cbn [cells_size csize Nat.add]. replace (A + Z.of_nat (Z.to_nat sz) + 1) with (A + sz + 1) by lia. exact H3.
    - cbn [cells_size csize Nat.add]. lia.
  Qed.
End K.
