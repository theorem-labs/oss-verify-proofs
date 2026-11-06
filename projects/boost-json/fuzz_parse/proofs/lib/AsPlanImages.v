(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Top0Gc4. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec StoreOk AgentLib AsanAcct AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums AsanHexScan AsanHexTree AsanInit AsImages AsPlanImagesHex AsPlanImagesHex2 AsPlanImagesHexZ.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypehe7Segment69OSSVerifyaboost_jsonafuzz_parse6images4Asan1M~~~~~~ldfloaded_segmentshe8PhdrInfold5phdrs79OSSVerify6Proofsaboost_jsonafuzz_parse3libcAsPlanImages4FPX1~~~~~~r75ASEGS69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanAcct~~~~~~hg3ewx_segs_nowrap37Corelib7Numbers7BinNumshl01Z04bool46Stdlib6ZArith6BinInt1Zhn44of_Nhe8seg_basehn43leb04andbhe8seg_size36Stdlib5Lists4Listhr77forallbhn43add37Corelib4Init5Logichtc2eq04None06option04truehtc2or3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsih0cfind_segmentr7esegs_in_hull_bhn42lehn42lt69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsImages~~~~~~in46ASAN_H79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanPlan2AP~~~~~~ir96img_hiir96img_lohl04Npos35stdpp9bitvectorbdefinitionsjh3bbv_unsigned05false79OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsanPlanSound3APS~~~~~~jk67in_hulljh32bvjk6ares_len_ok03fst04prod03sndhtc3and37Corelib5Lists7ListDefjs06Forall3h5LinuxProcessSemanticsfLinuxProcessSem3Runju1h1segments_reservedhtc2exhr72Injk67hull_okjk69shadow_okjk69sum_sizes79OSSVerify6Proofsaboost_jsonafuzz_parse3libh1AsanPlanSoundSums4APSX~~~~~~kl4asegs_wr_okhtc3nothl01Nih0bhex_byte_at59OSSVerifyaboost_jsonafuzz_parse6images4Asan~~~~~~ks7h2Asan_seg_bytes_00346Stdlib6NArith6BinNat1Nlh12lt04cons03nilks7h0Asan_segment_000ks7h0Asan_segment_001ks7h0Asan_segment_002ks7h0Asan_segment_003ih05wviewr73APH69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanInit~~~~~~lpd9img_facts03natir9emk_itab_ranges79OSSVerify6Proofsaboost_jsonafuzz_parse3libaAxSymExec33AX2~~~~~~lvcaitab_sound" s.
Import ListNotations.
Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition ASEGS : ltac2:(zQ "20!h8!l3@1$0$1") := ltac2:(zQ "10!p2$0").
Definition APH : ltac2:(zQ "10!q4$0") := ltac2:(zQ "10!qf$0").

Lemma asan_wx : ltac2:(zQ "20!vb!hje@1$1$0").
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition segs_in_hull_b : ltac2:(zQ "40!hm9!hme!h8!l3>4segs@1$2$3>2lo$0>2hi$0$1") := ltac2:(zQ "a0!l3!hoc!hm9!hp4!hpf!hq6!h8!hqc!hsa!ht5\4segs@1$6$0\2lo$2\2hi$2@3$8$0\3seg$0@2$5@2$4^3@1$1@1$3^1@2$4@2$9@1$1@1$3^1@1$1@1$7^1^2^3").

Lemma find_segment1_none_outside : ltac2:(zQ "d0!hm9!l3!hv0!hv6!hme!h8!hvc!ig4!iga!ik7!il7!im8!ime>4segs@1$5$1>2lo$0>2hi$0>1x$0>0@3$2$4@3$a^4^3^2$7>0@2$8@2$c^2^4@2$b^3^2@3$2@1$6$1@3$9^6^3+1@1$3$1").
Proof.
  induction segs as [|s l IH]; intros lo hi x Hb Hx; [reflexivity|].
  cbn [segs_in_hull_b forallb] in Hb. apply andb_true_iff in Hb as [Hs Hl].
  apply andb_true_iff in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  cbn [find_segment].
  replace (Z.leb (Z.of_N (seg_base s)) x && Z.leb (x + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool with false.
  - exact (IH lo hi x Hl Hx).
  - symmetry. apply andb_false_iff. destruct Hx as [Hx|Hx]; [left | right]; apply Z.leb_gt; lia.
Qed.

Lemma asan_segs_in_hull : ltac2:(zQ "80!iqf!hme!ig4!hv0!vb!il7!iv7!jg1@3$3$1@3$5$4@1$7$0@1$6$0$2").
Proof. vm_compute. reflexivity. Qed.

Lemma asan_in_hull : ltac2:(zQ "d0!jgb!hv0!l3!jj0!hv6!hme!jjf!hvc!ik7!iqf!vb!joa!jp5>1a@1$c@1$0#k0>0@3$1$5@2$b$9@2$3@1$0#k0^1$6@3$1@1$7$2@3$8$a@2$3@1$0#k0^2+1@1$4$2").
Proof.
  intros a H. apply (find_segment1_none_outside ASEGS (img_lo ASAN_H) (img_hi ASAN_H)); [exact asan_segs_in_hull|].
  unfold APS.in_hull in H. apply andb_false_iff in H as [H|H]; [apply Z.leb_gt in H; left | apply Z.ltb_ge in H; right]; lia.
Qed.

Lemma asan_res_len : ltac2:(zQ "30!iqf!vb!jpb@2$2$1$0").
Proof. vm_compute. reflexivity. Qed.

Lemma asan_res_hull : ltac2:(zQ "f3!jgb!jp5!jj0!jq9!jqe!iqf!im8!jr4!jr9!jt7!kgd!vb!iv7!jg1!ht5&@2$4@1$1@1$0#k0@1$1@1$0#k0&@3$3@1$1@1$0#k0@1$1@1$0#k0^1&@2$2@1$0#k0~1@3$9~0\2iv~0@2$8@2$6@1$d$5~2@2$6@2$e~2@2$2@1$0#k0@3$7@1$1@1$0#k0@1$1@1$0#k0^1@1$c$5@1$a$b").
Proof.
  assert (E : segments_reserved ASEGS = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x57000); (Z_to_bv 64 0x67000, Z_to_bv 64 0x146000);
                                         (Z_to_bv 64 0x1ad000, Z_to_bv 64 0xa000); (Z_to_bv 64 0x1b7000, Z_to_bv 64 0x55f000)])
    by (vm_compute; reflexivity).
  rewrite E. cbn [img_lo img_hi ASAN_H].
  repeat constructor; cbn [fst snd]; rewrite ?u64_lit by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma asan_res_cover : ltac2:(zQ "h23!jgb!jp5!jr9!iqf!jqe!ime!jj0!jq9!iv7!jg1!im8!jr4!ki3!hm9!kgd!vb!ki9!ht5&@2$4@1$1@1$0#k0@1$1@1$0#k0&@3$7@1$1@1$0#k0@1$1@1$0#k0^1&@2$6@1$0#k0~1@2$2@2$5@1$9$3@1$8$3>1z$d>0@2$2@2$a@1$9$3^1@2$5^1@1$8$3@2$c~0\2iv~0@2$2@3$h0~0^1@1$e$f@2$2@2$a~2^3@2$5^3@2$h1~2@2$6@1$0#k0@3$b@1$1@1$0#k0@1$1@1$0#k0^1").
Proof.
  assert (E : segments_reserved ASEGS = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x57000); (Z_to_bv 64 0x67000, Z_to_bv 64 0x146000);
                                         (Z_to_bv 64 0x1ad000, Z_to_bv 64 0xa000); (Z_to_bv 64 0x1b7000, Z_to_bv 64 0x55f000)])
    by (vm_compute; reflexivity).
  rewrite E. cbn [img_lo img_hi ASAN_H]. split; [lia|]. intros z Hz.
  destruct (Z_lt_le_dec z 0x67000);
    [exists (Z_to_bv 64 0x10000, Z_to_bv 64 0x57000) | destruct (Z_lt_le_dec z 0x1ad000);
    [exists (Z_to_bv 64 0x67000, Z_to_bv 64 0x146000) | destruct (Z_lt_le_dec z 0x1b7000);
    [exists (Z_to_bv 64 0x1ad000, Z_to_bv 64 0xa000) | exists (Z_to_bv 64 0x1b7000, Z_to_bv 64 0x55f000)]]];
    (split; [cbn [In]; tauto | cbn [fst snd]; rewrite !u64_lit by lia; lia]).
Qed.

Lemma asan_hull_ok : ltac2:(zQ "20!iqf!kif@1$1$0").
Proof. unfold APS.hull_ok. cbn [img_lo img_hi ASAN_H]. unfold KHI. repeat split; reflexivity || lia. Qed.

Lemma asan_shadow_ok : ltac2:(zQ "20!iqf!kja@1$1$0").
Proof. unfold APS.shadow_ok. cbn [shadow_off ASAN_H]. lia. Qed.

Lemma asan_res_sizes : ltac2:(zQ "50!hv0!hm9!kgd!vb!kk7@3$0$1@1$4@1$2$3+ngmgg0").
Proof. vm_compute. reflexivity. Qed.

Lemma asan_segs_wr : ltac2:(zQ "20!vb!kpe@1$1$0").
Proof. intros seg Hin Hw. cbn in Hin. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hw |- *; congruence. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition asan_hex3d_blocks : list (positive * nat) := [(1343%positive, 12%nat); (84%positive, 16%nat); (170%positive, 15%nat); (342%positive, 14%nat); (686%positive, 13%nat); (1374%positive, 12%nat)].
Lemma asan_hex3d_gallv : gallv Asan.Asan_seg_bytes_003 asan_hex3d_blocks.
Proof. unfold asan_hex3d_blocks. gallv_vm. Qed.
Lemma asan_hex3d : vpt Asan.Asan_seg_bytes_003 5500928 131072.
Proof. apply (vtree_scan_sound _ asan_hex3d_blocks); [exact asan_hex3d_gallv| vm_compute; reflexivity]. Qed.

Lemma asan_hex3_pt : ltac2:(zQ "a0!jgb!jp5!hv6!hvc!hv0!kqc!kr3!kr8!kva!li9>1i$6>0@2$9^1@1$0#llvgg0@1$5@3$4@1$3@1$1@1$0#8@2$7$8^2@1$2@1$1@1$0#8").
Proof.
  intros i Hi.
  destruct (N.lt_ge_cases i 42112) as [H1|H1]; [exact (asan_hex3a i H1)|].
  destruct (N.lt_ge_cases i 570544) as [H2|H2].
  { replace i with (42112 + (i - 42112))%N by lia. apply (zpt_vpt _ _ _ asan_ia_zero). lia. }
  destruct (N.lt_ge_cases i 962904) as [H3|H3].
  { replace i with (570544 + (i - 570544))%N by lia. apply asan_hex3b. lia. }
  destruct (N.lt_ge_cases i 5157208) as [H4|H4].
  { replace i with (962904 + (i - 962904))%N by lia. apply (zpt_vpt _ _ _ asan_tab_zero). lia. }
  destruct (N.lt_ge_cases i 5500928) as [H5|H5].
  { replace i with (5157208 + (i - 5157208))%N by lia. apply asan_hex3c. lia. }
  replace i with (5500928 + (i - 5500928))%N by lia. apply asan_hex3d. lia.
Qed.

Lemma asan_segs_eq : ltac2:(zQ "a0!l3!lif!h8!lj5!hv0!vb!lja!lkf!lm4!ln9@3$4@1$2$0$5@3$1$0$6@3$1$0$7@3$1$0$8@3$1$0$9@1$3$0").
Proof. reflexivity. Qed.

Lemma asan_rw_window : ltac2:(zQ "c0!jgb!jp5!hvc!jj0!hv6!jr9!hv0!kqc!loe!vb!im8!ime>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8>1x@1$1@1$0#k0>0@2$5@2$a+hqtgg0@2$3@1$0#k0^1@2$b@2$3@1$0#k0^1+nhmgg0@1$7@3$6@1$2@1$1@1$0#8@3$8$9^3^2@1$4@1$1@1$0#8").
Proof.
  intros m x Hx. unfold wview. destruct (m x); [discriminate|].
  destruct (find_segment ASEGS (bv_unsigned x) 1) as [seg|] eqn:Hf.
  - apply find_segment_some_spec in Hf as (Hin & Hb & Ht).
    rewrite asan_segs_eq in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
      cbn [seg_base seg_size seg_writable seg_perms seg_bytes string_has Ascii.eqb
           Asan_segment_000 Asan_segment_001
           Asan_segment_002 Asan_segment_003] in Hb, Ht |- *.
    + exfalso. lia.
    + exfalso. lia.
    + cbn -[segment_byte_at]. apply (segment_byte_at_some_pt _ 40960); [exact asan_hex2 | rewrite asan_len2; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
    + cbn -[segment_byte_at]. apply (segment_byte_at_some_pt _ 5632000); [exact asan_hex3_pt | rewrite asan_len3; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
  - exfalso. destruct (Z.lt_ge_cases (bv_unsigned x) 0x1b7000) as [Hl|Hl].
    + apply (find_segment_none_spec _ _ _ Hf Asan_segment_002);
        [rewrite asan_segs_eq; cbn; tauto | cbn; lia].
    + apply (find_segment_none_spec _ _ _ Hf Asan_segment_003);
        [rewrite asan_segs_eq; cbn; tauto | cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma asan_img_facts : ltac2:(zQ "40!iqf!lp7!vb!lt8@3$3$2$0$1").
Proof.
  constructor.
  - repeat split; reflexivity.
  - cbn [img_lo img_hi ASAN_H]. lia.
  - vm_compute. reflexivity.
  - exact asan_res_hull.
  - rewrite asan_res_sizes. reflexivity.
  - cbn [rw_lo rw_len ASAN_H]. split; [lia|]. intros m x Hx. apply asan_rw_window. lia.
  - exact asan_shadow_ok.
Qed.

(* [comment removed for export] *)
Lemma itab_ranges_ok : ltac2:(zQ "70!vb!h8!lu5!jqe!hm9!lua!mjd>2rs@1$1@2$3$4$2@2$6$0@2$5$0^1").
Proof. intros rs. apply APS.mk_itab_ranges_sound. Qed.
End FPX1.
