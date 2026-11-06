(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim MmapSim AllocSim Scfg ShapeAlg SpinAlg AgentLib RefNodes.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import Prelim Monad STree Malloc Prog KInv KStep.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge Require Import BrRegs BrBase BrNodes KLink BrRes.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Bridge_Embed () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge.Embed.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge.Embed.CEIL_WRAP_1.EVENTS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge.KLink."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Decode."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.ITree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Nodes."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.KInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Monad."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Prog."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.MmapSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefNodes."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0CAPB"; "0CAPK"; "1None"; "1S"; "1Some"; "1app"; "1bool"; "1cons"; "1false"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"]; ["1true"; "1unit"; "2and"; "2eq"; "2ex"; "2or"; "3le"; "4Forall"; "5Z"; "0K"; "0L"; "6machine_state"; "7mkCfg"; "8MemCopy"; "8Model"; "8SyscallEffect"]; ["8VmMaps"; "8alloc_top"; "8live_bytes"; "8m_halted"; "8m_vm_lazy"; "8m_vm_materialized"; "8m_vmmaps"; "8map_remove"; "8maps_subtract"; "8mkEffectU"; "8mkVmMapsFull"; "8page_size"; "8region_free"; "8vm_brk"; "8vm_init_sp"; "8vm_limit"]; ["8vm_maps"; "8vm_mmap_base"; "8vm_noaccess"; "8vm_reserved"; "8vm_start_brk"; "8with_vmmaps"; "9brk_grow_ok"; "0RUNp"; ":CAPBMAX"; ":CAPKMAX"; ";vm_shrunk"; ":NMAX"; ":RI"; "<KL2"; "=BrkGrown"; "=BrkSame"]; ["=MmOk"; "=RgDone"; "=brk_ans"; "=dec_brk"; "=dec_brk0"; "=dec_mmap"; "=dec_mmap_none"; "=dec_munmap"; "=mmap_addr_ok"; "=mmap_ans"; "=mmap_len"; "=range_ans"; ">msteps"; "?nret"; "@NBrk"; "@NMmap"]; ["@NMprotect"; "@NMunmap"; "@at_node"; "Aalloc_ceiling"; "BBPGuard"; "BBPQueried"; "BBPUntried"; "BLEN_MAX"; "BMAPF"; "BMAPFX"; "Banswer_ok"; "Bbrk_phase"; "Bbrk_quiet"; "Bevent_post"; "Bld_brk"; "Bld_groups"]; ["Bld_metas"; "Blranges"; "Bmled"; "Bset_brkph"; "Bset_groups"; "Bset_metas"; "CEBrk"; "CEMmap"; "CEMprotect"; "CEMunmap"; "CMAP_FIXED"; "CPGSZ"; "CPROT_NONE"; "CPROT_RW"; "Cbrk0_answer_ok"; "Cev"]; ["Cis_err"; "Cmmap_answer_ok"; "Cround_up_pg"; "DM"; "Dmbind"; "Dmret"; "Dmsys"; "Dmupd"; "EFxDone"; "EPState"; "Edec_mmap_fixed"; "Edec_mprotect_rw"; "Eev_step"; "Efixed_ans"; "Eset_brk_ps"; "Fgrant_ok"]; ["Ggrant_ok_na"; "HTSet"; "Isrealizes"; "JIn"; "Kadd"; "Keqb"; "Kland"; "Kle"; "Klt"; "Kmodulo"; "Kmul"; "Kpow"; "Ksub"; "0a"; "0addr"; "0aw"]; ["0b"; "0bb"; "0bb'"; "0br"; "0cur"; "0d"; "0e"; "0h"; "0h'"; "0h0"; "0h1"; "0h2"; "0img_hi"; "0k"; "0l"; "0l0"]; ["0len"; "0m"; "0mo"; "0mo0"; "0ms"; "0ms'"; "0n"; "0na"; "0ne"; "0ne'"; "0nw"; "0p"; "0pbrk"; "0prot"; "0r"; "0req"]; ["0resv_img"; "0rsp"; "0sb"; "0scfg"; "0segs"; "LZ_to_bv"; "Lbv"; "Lbv_unsigned"; "0z"]]).
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition NMAX : Z := 2^27 + 2^16.
Definition CAPKMAX : Z := 8200.
Definition CAPBMAX : Z := 2^33.
Lemma NMAX_facts : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "C'B&T8z&QK%3221'C'H&T9&Q;%2261%53418&T7&T:+2&S;%3221%521=%A271%B2>1").
Proof. unfold NMAX, PGSZ, page_size. split; [lia|]. split; [reflexivity| lia]. Qed.
Lemma NMAX_le_30 : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "7&T7&QK&T;+2+N%3221%6251"). Proof. unfold NMAX. lia. Qed.
Lemma CAPKMAX_le : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "4&T7&QI+QWR0%3221"). Proof. unfold CAPKMAX. lia. Qed.
Lemma Forall_size_30 : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "L'9'>'UFyR0%211%4211%611'G&T7&UG&?r1%23881%42:1&QK%7221qZH;1%:3<16&T;+2+N%3221%>291qZHB1r2%B3D21p091pYNE1").
Proof. intros l H. eapply Forall_impl; [|exact H]. intros p Hp. cbn in Hp |- *. pose proof NMAX_le_30. lia. Qed.
Section IMPL.
Variable segs : list Segment.
Context {St : Type}.
Lemma implM_ret_inv : forall {A} (a : A) (s : St) Q ms,
implM segs (mret a) s Q ms -> evt segs (Q a s) ms.
Proof. intros A a s Q ms H. exact H. Qed.
Lemma implM_bind_inv : forall {A B} (m : Monad.M St A) (f : A -> Monad.M St B) s Q ms,
implM segs (mbind m f) s Q ms ->
implM segs m s (fun a s' ms' => implM segs (f a) s' Q ms') ms.
Proof.
intros A B m f s Q ms H. unfold implM, mbind in *. apply impl_ebind_inv in H.
eapply impl_mono; [exact H|]. intros [|[a s']] ms'; cbn; auto.
Qed.
Lemma implM_msys_inv : forall {A} n (dec : resp -> option A) (s : St) Q ms,
implM segs (msys n dec) s Q ms ->
evt segs (fun ms1 => at_node segs n ms1 /\ forall rsp a, dec rsp = Some a -> evt segs (Q a s) (nret ms1 rsp)) ms.
Proof.
intros A n dec s Q ms H. unfold implM, msys in H. apply impl_enode_inv in H.
eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
intros rsp a E. apply (Hk rsp (a, s)). rewrite E. reflexivity.
Qed.
Lemma mbind_mget : forall {A} (f : St -> Monad.M St A) s, mbind mget f s = f s s.
Proof. reflexivity. Qed.
Lemma implM_mget_inv : forall {A} (f : St -> Monad.M St A) s Q ms,
implM segs (mbind mget f) s Q ms -> implM segs (f s) s Q ms.
Proof. intros A f s Q ms H. exact H. Qed.
Lemma implM_mupd_inv : forall {A} g (m : Monad.M St A) s Q ms,
implM segs (mbind (mupd g) (fun _ => m)) s Q ms -> implM segs m (g s) Q ms.
Proof. intros A g m s Q ms H. exact H. Qed.
Lemma mbind_mupd : forall {A} g (m : Monad.M St A) s, mbind (mupd g) (fun _ => m) s = m (g s).
Proof. reflexivity. Qed.
Lemma mbind_mret_l : forall {A B} (a : A) (f : A -> Monad.M St B) s, mbind (mret a) f s = f a s.
Proof. reflexivity. Qed.
End IMPL.
Lemma with_vmmaps_twice : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed ">'Q0'N'C&QEr2r3r1%4221%5241%6253%83921pZ4:1pYH<1pYF=1").
Proof. intros h1 h2 m. reflexivity. Qed.
Lemma with_vmmaps_mat : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "B'Q0'N'C'9'UFyR0%211%411&Q5&QEr2r1%3221%511%613%=3821pZ4?1pY@A1").
Proof. reflexivity. Qed.
Lemma live_bytes_cons' : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "I'>'UFyR0%211%4211'9%112'C'H&Q2(7r2r1%33921%511&T4&UG&?%13??7%32A1%;18%6221%?3>81pYNA1pY>D1").
Proof. intros [a n] l. reflexivity. Qed.
Lemma Forall_app_cons_mid : forall {A} (P : A -> Prop) l1 x l2,
Forall P (l1 ++ l2) -> P x -> Forall P (l1 ++ x :: l2).
Proof.
intros A P l1 x l2 H Hx. apply Forall_app in H as [H1 H2]. apply Forall_app. split; [exact H1|]. constructor; assumption.
Qed.
Lemma length_app_cons_mid : forall {A} (l1 : list A) x l2, length (l1 ++ x :: l2) = S (length (l1 ++ l2)).
Proof. intros. rewrite !length_app. cbn. lia. Qed.
Lemma Forall_filter : forall {A} (P : A -> Prop) f l, Forall P l -> Forall P (List.filter f l).
Proof. intros A P f l H. induction H; cbn; [constructor|]. destruct (f x); [constructor|]; auto. Qed.
Lemma length_filter_le : forall {A} f (l : list A), (length (List.filter f l) <= length l)%nat.
Proof. intros. apply List.filter_length_le. Qed.
Definition RI (CAPK CAPB : Z) (ne : nat) (bb : Z) (h : VmMaps) : Prop :=
Z.of_nat (length (vm_reserved h ++ vm_maps h)) + Z.of_nat ne <= CAPK
/\ Forall (fun p => bv_unsigned (snd p) <= NMAX) (vm_reserved h ++ vm_maps h)
/\ live_bytes (vm_maps h) + bb <= CAPB
/\ 0 <= bb
/\ CAPBMAX <= vm_limit h
/\ sp_window_lo <= bv_unsigned (vm_init_sp h).
Lemma RI_weaken : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "Q0'H':'Q0&QLr7r6r5r3r1%6554321'F%1256'B&T7zr4%3221%422;%6221r:r9%B521A?6p041p0<1p0?1pY@G1pY6J1pY4K1pZDK1pZBL1p2N1p4O1").
Proof. intros CAPK CAPB ne ne' bb bb' h (R1 & R2 & R3 & R4 & R5 & R6) Hne Hbb. unfold RI. splits; auto; lia. Qed.
Lemma RI_add : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "R8'H':'Q0'UFyR0%211'9'>%1233%311&QLr:r9(3r8%211r7r6%8576321'B&T7zr5%3221&QK%5231%7231%72:?'C&UG&UE%12K?%32L1%53Q11Ar>r=r<&T<r;%221I(Q:&QC%11O(7(=%?2Q9O%24Q9Q9Q21&Q@%11Q5%63Q931&Q?%11Q8&QA%11Q:&Q>%11Q<%@8>7Q8Q7Q2531%Q?5GFEB1p0I1p0Q01p0Q21p0Q;1pY8QI1p[6QJ1pZ@QG1pZ>R11pXLQM1pY@R11pY4R41pZBR41p2R61p4R71").
Proof.
intros CAPK CAPB ne bb h a n na sb br (R1 & R2 & R3 & R4 & R5 & R6) Hn Hnb Hu. unfold RI.
cbn [vm_reserved vm_maps vm_limit vm_mmap_base vm_init_sp].
rewrite length_app_cons_mid, live_bytes_cons'. cbn [snd]. rewrite Hu. splits; auto; try lia.
apply Forall_app_cons_mid; [exact R2| cbn [snd]; rewrite Hu; lia].
Qed.
Lemma RI_tick : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "QE'H':'Q0'9'>'UFyR0%211%4211%611&QLr9r8(3r7%211r6r4%8576321'B&T7z%2216%3279%5221r;r:(Q:&QC%11=&Q@%11?r5r3&Q?%11C&QA%11E&Q>%11G%=8;98G7531%O5@?NK1p0B1p0I1pY8Q51p[6Q61pZ@Q51pY@Q=1pY6Q@1pY4QA1pZBQA1p2QC1p4QD1").
Proof.
intros CAPK CAPB ne bb bb' h na sb br (R1 & R2 & R3 & R4 & R5 & R6) Hbb. unfold RI.
cbn [vm_reserved vm_maps vm_limit vm_mmap_base vm_init_sp]. splits; auto; lia.
Qed.
Lemma RI_remove : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "QI'H':'Q0'UFyR0%211'9'>%1233%311&QLr:r9(3r8%211r7r5%8576321'B&T7z%2216%3279%5221r<r;(Q:&QC%11=&Q7&Q@%11@r6%4221r4r3&Q?%11F&QA%11H&Q>%11J%@8>9J87531%Q25CBQ1N1p0E1p0L1pY8Q:1p[6Q;1pZ@Q81pY0Q=1pY@QA1pY6QD1pY4QE1pZBQE1p2QG1p4QH1").
Proof.
intros CAPK CAPB ne bb bb' h aw na sb br (R1 & R2 & R3 & R4 & R5 & R6) Hbb. unfold RI.
cbn [vm_reserved vm_maps vm_limit vm_mmap_base vm_init_sp].
pose proof (RefNodes.live_bytes_map_remove_le (vm_maps h) aw) as Hlb.
unfold map_remove in *. pose proof (length_filter_le (fun p : word * word => negb (bv_eqb (fst p) aw)) (vm_maps h)) as Hlen.
rewrite length_app in R1 |- *. splits; auto; try lia.
apply Forall_app in R2 as [R2a R2b]. apply Forall_app. split; [exact R2a| apply Forall_filter; exact R2b].
Qed.
Lemma RI_grant_rw : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "R5'H':'N&QLr6r5r4r3&Q6r2%211%8576541&T7r7&QI%3221&QH%5241'C'9'>'UFyR0%211%4211%611&Q4%11F(;%115%<3531%<18&Q5%11M%61;%A3421'Bz%J21Q2&QK%L2Q41%5231r9%O2N1'D'6&SO&UE%12J;r:r1%543219(@%Q33821qXLO1%;2Q01p0=1p0@1p0G1p0M1p0Q;1p0Q>1p0QC1pZ>QO1pZ6QN1pY4R11pZBR11p2R31p4R41").
Proof.
intros CAPK CAPB ne bb mo n (R1 & R2 & R3 & R4 & R5 & R6) HK HB' Hl Hm Hn Hnb.
pose proof NMAX_le_30. pose proof CAPKMAX_le.
apply (grant_exists (Z_to_bv 64 0) mo n R6); [lia| apply Forall_size_30; exact R2| lia|].
apply RefNodes.grant_budget_intro; [exact Hl| exact Hm|]. unfold vm_live_bytes. lia.
Qed.
Lemma RI_grant_na : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "Q>'H':'N&QLr6r5r4r3&Q6r2%211%8576541&T7r7&QI%3221'Bz%621;&QK%82=1%5231'D'UFyR0%211'C'6&T0&UE%126=r1%442L1K(@%83721qXL:1%>2;1p0@1p0G1p0L1pZ>Q81pZ6Q71pY4Q:1pZBQ:1p2Q<1p4Q=1").
Proof.
intros CAPK CAPB ne bb mo n (R1 & R2 & R3 & R4 & R5 & R6) HK Hn.
pose proof NMAX_le_30. pose proof CAPKMAX_le.
apply (grant_exists_na (Z_to_bv 64 0) mo n R6); [lia| apply Forall_size_30; exact R2| lia].
Qed.
Lemma RI_live_limit : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "M'H':'Q0&QLr5r4r3r2r1%6554321&T7&QH%2281&T4&Q2&Q@%11:%311%521=&Q?%11>%;231p0:1p0>1pY@F1pY4I1pZBI1p2K1p4L1").
Proof. intros CAPK CAPB ne bb h (R1 & R2 & R3 & R4 & R5 & R6) HB. lia. Qed.
Section SE.
Variables (m : Model).
Variables (d : Z).
Lemma brk_grow_ok_aligned_elim : let h := m_vmmaps m in
let b := vm_brk h in
bv_unsigned b mod page_size = 0 -> d mod page_size = 0 -> 0 < d -> 0 < bv_unsigned b ->
bv_unsigned b + d < 2 ^ 64 ->
Mmap.brk_grow_ok m (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true ->
bv_unsigned b + d <= alloc_top h
/\ region_free (vm_reserved h ++ vm_maps h) b (Z_to_bv 64 d) = true.
Proof.
intros h b Hbal Hdal Hd Hb0 Hnw H.
assert (Hureq : bv_unsigned (Z_to_bv 64 (bv_unsigned b + d)) = bv_unsigned b + d) by (apply u64_lit; lia).
unfold Mmap.brk_grow_ok, Mmap.brk_budget_ok in H. fold h in H. fold b in H. rewrite Hureq in H.
rewrite (proj2 (Z.ltb_lt 0 _) Hb0), (proj2 (Z.ltb_lt (bv_unsigned b) _)) in H by lia. cbn [andb] in H.
rewrite (page_round_up_Z_aligned (bv_unsigned b)) in H by (first [lia | exact Hbal]).
rewrite (page_round_up_Z_aligned (bv_unsigned b + d)) in H
by (first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
rewrite (proj2 (Z.ltb_lt _ _)) in H by lia.
replace (Z_to_bv 64 (bv_unsigned b)) with b in H by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
replace (bv_unsigned b + d + page_size - bv_unsigned b) with (d + page_size) in H by lia.
apply andb_prop in H as [H _]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. split; [exact H1|].
assert (Hb4 : page_size <= bv_unsigned b) by (clear - Hbal Hb0; unfold page_size in *; Z.div_mod_to_equations; lia).
eapply AllocSim.region_free_prefix; [| exact H2]. rewrite !u64_lit by (unfold page_size in *; lia). unfold page_size; lia.
Qed.
End SE.
Section EVENTS.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Hypothesis Halloc : sc_alloc scfg = false.
Variable resv_img : list (word * word).
Variable img_hi : Z.
Variable CAPK CAPB : Z.
Hypothesis HCAPK : CAPK <= CAPKMAX.
Hypothesis HCAPB : CAPB <= CAPBMAX.
Local Notation KL := (KL2 resv_img img_hi).
Lemma step_brk0 : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "SF'S2'H'K'N&T1'QMvQGvU@vTLr5r4&Q6r2%211%96876541'C'RK&RNr6%211(RF%63521'<'UFyR0%211%411&Q3%11B(2%115%@3531'9'>%1299%311&Q4%11L(;%115%I3531&RBvUD(R>z%211r7%63521&UG&Q=%Q714%211%42L1'O(Q9r8%Q=11%811y8%Q411%L11%L2Q41%H11'M%J11':%Q12Q91%M11%>6;6MM41%Q?1R4&R4r1%211(4%12R9QN%QL3631'6&S>r3%211(@%R23521&S3(RE%11R:r>%4221r;%R=11%RD6RCRBRA3R?1'T2vUC(L&R=r=%221REr<%5221%84QH71;p0:1p0C1p0J1t[4QAQ21tZNS6QC1r9%=21QB%@4R0?1QLp041p0QM1p0R51p0R?1p0RJ1p0S21pQDS=1pZ6S?1pZ:SA1pZJSC1pQFSE1").
Proof.
intros L pbrk ms mo K HK Hph Hh Hl Hat HC.
destruct (KL2_brk0 resv_img img_hi L pbrk (m_vmmaps mo) HK Hph) as [Hans HK'].
eapply (bn_brk_query segs scfg); [exact Hh| exact Hl| exact Hat|].
apply HC; [reflexivity| exact Hans| exact HK'].
Qed.
Lemma dec_brk_same : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "Q:'H'UFyR0%211'C&UGr1%2251r3%53921'<'R2%211&R3r4(Q9r2(;'>'9y8%D11%311%52D1%711%72FF%911'M%;11':%<2K1%>11%A6@86641%D3CI1(4(QO%22I1%Q13I41p0M1pY2Q41p[0Q81pY:Q91").
Proof. intros cur req b Hb. unfold dec_brk. rewrite Hb, Z.eqb_refl. reflexivity. Qed.
Lemma dec_brk_grown : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "R:'H'UFyR0%211'C&UGr1%2251r3%53921&T9r4&Q;%3221z%;3?21&T8r5%2241&T7r7%2271&T4r8%2214&T;+2+R0%3221%=251'<'R2%211&R3r9%=21<(Q9&UE%12Q43(;'>'9y8%Q:11%311%52Q:1%711(7%82Q=Q=(=%=2Q@K%24Q@Q@O1%=14%63521'M%@11':%A2QF1%C11%G6E=6741%K3JI1(4(QN%22Q01%QL3Q041p0Q41p0Q=1p0QA1p0QE1p0QF1p0QM1pY2R41pY<R81pY:R91").
Proof.
intros cur d b Hb Hcal Hdal Hd Hc Hnw. unfold dec_brk.
rewrite u64_lit by lia. replace (cur + d =? cur) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
rewrite Z.eqb_refl. unfold brk_new_pages.
rewrite (page_round_up_Z_aligned cur) by (first [lia | exact Hcal]).
rewrite (page_round_up_Z_aligned (cur + d)) by (first [lia | rewrite Z.add_mod, Hcal, Hdal by (unfold page_size; lia); reflexivity]).
rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [zeros_of]. replace (cur + d - cur) with d by lia.
unfold wa. rewrite <- Hb, Z_to_bv_bv_unsigned. cbn [listNN_eqb]. rewrite !bv_eqb_refl. reflexivity.
Qed.
Lemma step_brk_grow : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "XO'S2'H'K'N':&T1'S?(S6&T4&UGyR0&Q=&Q6r5%211%411%7261r4%:221%<11'Q0r6%:11'UF%11>r1%?11%B2A2r7%E221'QMvQGvU@vTLr<r;r3%76654321'C'<%11@&Q3r:%211(2%11E%83631'9'>%12II%311&Q4%11A(;%115%A3531%91Q0&Q5%11H%61Q3%F3421&QLv1v0(3%11N%55431HQ6&T7r=%221Q2'B&T8zr>%3221&QK%9231%7231&T9r?&Q;%3221%Q<3RA1:rC%R;2R:Q:%Q?3RD21%R=2R<QC&S;%:221%QC3RH1A%RA2R@QH%D2C1%RC2RBH%RE21:&T;+2+R0%3221%K251&QD%11E%RL2RK1%RM2RLMrD%S0221%Q6241'6&RJrIrArH%44R@321(@%R;3721&RM%13765r@%RG6RFRERD271%Q@251&Q<&5&QC%11=&Q@%11?%53R<31&UErF%22SF1%:34=1%RL3H1B%SJ2SIFrG%SM221&RC%11S8%R5231rL%O4S;1Q3M%S53Q11K%J33Q5O(Q:%E1QK(7(=rB%D2T8Q4%34SKSK21%I1R1%63S421&QB%11R4%QE1R5%K2T?Q<&Q?%11R8&QA%11R:&Q>%11R<%C8B;987531%T36T2T1T0EQD1%RL2G1p0K1p0Q21&RBvUD(R>%11QD%4331QM'O(Q9y8%TF11%SO11%SO2TG1%SK11'M%SM11%T32TKU?%SO11%:6Q45SOSO31'R2%T@11&R3%13Q@Q8U0(4(QO%2261%TG3641rNrM%RE4U12R11%TK3RG1RArO%RA31QO5%U66U5U4U316R5rKrJ%T:5T9T821R3'T2vUC(L&R=%12:UO%321?%64Q8518p081p0<1p0@1p0E1t[4Q9N1%RF2V:R3%RG2V;S9%R64UNUNT31%R83U61U1%Q=64Q81U2Q6Q4rE%S111%RM2VAE%R<4V4V4SE1%S214%R?3U=21%R916%SM17%S32VGT>%R819%R71:%R61;%RH8;7654321r2%Q?3Q9T01(QN%Q?2QC1%V43QC31rQ0%T14V=1SNC%V73T31SMrQ1%SM31T3S@%VB6VAV@V?1SAV<&T<%12S9QD%UF5UEUDQD1W2%Q926VO&QE%12W9;%Q=231%Q@4RBQ?1S?p061p0:1p0>1p0B1tYBW9H1t[4RDQ61%QE2SFQJ%QH4RJQG1SLp031p0Q?1p0RJ1p0S01p0T?1p0TM1p0U51p0U=1p0U@1p0UE1p0UI1p0UO1p0V81p0V<1p0VC1p0VI1p0W31p0W=1t[0XBWF1tY2WLWJ1tY@X1WO1tY>X@X31pQDXB1pY4XG1pZBXE1pY<XI1pZ6XH1pZ:XJ1pZJXL1pQFXN1").
Proof.
intros L pbrk ms mo d ne bb K e h b req HK Hh Hl Hm HRI Hdb Hd Hdal Hpb Hbal Hb0 Hnw Hsb [HansR HKR] HG Hat HREF HGRANT.
pose proof (u64_range b) as Hbr.
assert (Hbal' : bv_unsigned b mod page_size = 0) by (unfold page_size; unfold PGSZ in Hbal; exact Hbal).
eapply (bn_brk_grow segs scfg Halloc ms mo d K Hh Hl); [exact Hat| exact Hbal'| exact Hdal| lia| exact Hb0| exact Hnw| exact Hsb| |].
-
apply HREF; [apply dec_brk_same; symmetry; exact Hpb| exact HansR| exact HKR|].
eapply (RI_weaken CAPK CAPB (S ne) ne bb bb); [| lia| pose proof HRI as (_ & _ & _ & R4 & _); lia].
subst h. rewrite <- (vmmaps_eta (m_vmmaps mo)) in HRI. exact HRI.
-
intros Hadm.
destruct (brk_grow_ok_aligned_elim mo d Hbal' Hdal ltac:(lia) Hb0 Hnw Hadm) as [Hce Hrf].
change (m_vmmaps mo) with h in Hce. rewrite (KL2_alloc_top _ _ _ _ _ HK) in Hce.
destruct (HG Hrf Hce) as [HansG HKG].
apply HGRANT; [| exact HansG| exact HKG|].
+ rewrite Hpb. apply dec_brk_grown; first [reflexivity| assumption| lia].
+ apply RI_add; [exact HRI| lia| exact Hdb| apply u64_lit; lia].
Qed.
Lemma land_MAPF : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed ";'C'6&T5&T6&RH&S:%3221z%6221(@%:3921").
Proof. reflexivity. Qed.
Lemma answer_ok_mmap : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "I'S2'H'C'6&RJvQGr5(S7r4r3r2&RH%544321r1%:49821&SA&S1%11;%34=195%A3@51p[BC1pZLD1pZ2E1pXLF1pQFH1").
Proof. intros. unfold answer_ok. rewrite land_MAPF. reflexivity. Qed.
Lemma event_post_mmap_rw : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "Q2'S2'H'C'6&S@r1%211(8%63521&RMr4(S7zr3&S=&RH%544321r2%93821&S4(7'>%12EE(=%14GG7;&RO%11@%73531%921B%K3M;1p0F1p[BN1pZ2O1pQFQ11").
Proof. intros L len z Hz. unfold event_post. rewrite land_MAPF, Hz. reflexivity. Qed.
Lemma event_post_mmap_none : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "Q4'S2'H'C'6&S@r1%211(8%63521&RMr4(S7zr3&S<&RH%544321r2%93821&S5(7'>%12EE%221F(=%14HH8<%244I1>&S0%11B%93631%;21D%M3O=1p0H1p[BQ01pZ2Q11pQFQ31").
Proof. intros L len z Hz. unfold event_post. rewrite land_MAPF, Hz. reflexivity. Qed.
Lemma mmap_addr_ok_nil : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "Q='H'UFyR0%211'C&T9&UGr1%2261&Q;%5221z%83<21&T8r2%92=1%3251&T7&T4r3%>2B1&R:r4%211%6241&RCvQG%211%;241'6&R8r5(;'>%12Q2Q2%311%N2Q2>%74;621(@%Q33:21p0<1p0I1p0N1pXLQ81pZ2Q<1").
Proof.
intros len a H1 H2 H3. unfold mmap_addr_ok. rewrite H1, Z.eqb_refl. rewrite (proj2 (Z.ltb_lt _ _) H2).
rewrite (proj2 (Z.leb_le _ _) H3). reflexivity.
Qed.
Lemma dec_mmap_ok : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "R8'H'UFyR0%211'C&T9&UGr1%2261&Q;%5221z%83<21&T8r2%92=1%3251&T7&T4r3%>2B1&R:r4%211%6241&RCvQG%211%;241'<'R9%211&R5r5(;'>%12Q4Q4%311(Q9'9y8%Q811%311%82Q81%:11(7%;2Q;Q;(=&UE%L1@%22Q@1%44Q@Q@M1%B16%83721'M%E11':%F2QF1%H11%E6Q5?6741%L4Q2KG1(4(R0%QI2QMQ9%211%42Q31%QN3Q361p0Q71p0QD1p0QI1pXLR31pZ2R71").
Proof.
intros len a H1 H2 H3. unfold dec_mmap. rewrite !bv_eqb_refl, (mmap_addr_ok_nil len a H1 H2 H3). reflexivity.
Qed.
Lemma dec_mmap_none_ok : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "R8'H'UFyR0%211'C&T9&UGr1%2261&Q;%5221z%83<21&T8r2%92=1%3251&T7&T4r3%>2B1&R:r4%211%6241&RCvQG%211%;241'<'R9%211&R6r5(;'>%12Q4Q4%311(Q9'9y8%Q811%311%82Q81%:11%:2Q:Q:%<11(7(=&UE%M1A%22QA1%44QAQAN1%63817'M%E11':%F2QF1%H11%E6Q5?=641%L4Q2KG1(4(R0%QI2QMQ9%211%42Q31%QN3Q361p0Q71p0QD1p0QI1pXLR31pZ2R71").
Proof.
intros len a H1 H2 H3. unfold dec_mmap_none. rewrite !bv_eqb_refl, (mmap_addr_ok_nil len a H1 H2 H3). reflexivity.
Qed.
Lemma step_mmap_rw : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "V>'S2'H'K'N':&T1'S?(S7zr4&S=&RH%544321'Q0&Q6r6%211&R:%113'QMvQGvU@vTLr;r:r2%76654321&RLr<%211'B&T8r9%22I1&RG%4231%6231'C'<'UFyR0%211%411&Q3%11E(2%115%:3531'9'>%1299%311&Q4%11I(;%115%C3531%91@&Q5r=%211%71D%I3521&QLv1v0(3%11Q7r8%65542Q>1&T7%123Q;&QK%32Q91&RBvUD(R?r@+3+Q2%44R8321rB%83721&UGr1%22Q=1'O(Q9y8%QB11%Q:11%Q:2QB1%Q611(7(=&UE%12QHQ5%34QHQHR81%53Q@1Q;'M%Q>11%QD2QLS1%Q@11%@6R>;5Q@31(Q:&QCr?%211r3r>%?2R61%A4R6R631&Q@%117%E3R031&QB%11:&QD%11<&Q=%11>&Q?%11@&QA%11B&Q>%11D%G8D=;97531'R9%RK11&R5rE%RC2T3T3%R?11%44SB31S=(4(R0%11M%32:1%S63:51'6&RJrJ%24SK1QNT6(@%S<3521&S@r5%211(8%SA3:21&RMrLrD%3321T;rK%T96T8T7T621TCrH&T<rGrC%3221%S35S2S151?'T2vUC(L&R=r7%22@1&QE%12TK?%6231%94S181=p0;1p0B1p0I1p0O1p0Q61tYBU5QC1t[4RMR<1t[BUCRO1pXLT<1%A2MF%D4S<C1R=p031p0S71p0SA1p0SD1p0SG1p0SO1p0T61p0T@1p0TL1p0U41p0U81tZ>V2UA1tY@UGUD1tY>UOUI1pQDV11pY4V61pZBV41pZ2V81pZ6V71pZ:V91pZJV;1pQFV=1").
Proof.
intros L pbrk ms mo len ne bb K e h n HK Hq Hlen Hh Hl Hm HRI Hnb HnN Hat HC. subst e.
pose proof (mmap_len_ge len ltac:(lia)) as Hn1. fold n in Hn1.
assert (HnA : n mod page_size = 0) by (unfold n; apply mmap_len_aligned).
assert (Hun : bv_unsigned (Z_to_bv 64 n) = n) by (apply u64_lit; unfold NMAX in HnN; lia).
eapply (bn_mmap_rw segs scfg Halloc ms mo len K Hh Hl Hat); [unfold LEN_MAX in Hlen; lia| |].
- change (page_round_up_Z len) with n. eapply (RI_grant_rw CAPK CAPB (S ne) bb mo n HRI HCAPK HCAPB Hl Hm); lia.
- intros a Hg. change (page_round_up_Z len) with n in Hg |- *.
destruct (grant_ok_unpack _ _ _ _ Hg) as (G1 & G2 & G3 & G4 & G5).
fold h in G3. rewrite (KL2_alloc_top _ _ _ _ _ HK) in G3.
destruct (KL2_mmap_new resv_img img_hi L pbrk h a len false HK Hq Hlen
ltac:(unfold PGSZ; unfold page_size in G1; exact G1) G2 G3 G4) as (HK' & Hans & Herr).
unfold mmap_model. fold h. apply HC.
+ apply dec_mmap_ok; [exact G1| exact G2| exact G3].
+ rewrite answer_ok_mmap. exact Hans.
+ exact Herr.
+ rewrite (event_post_mmap_rw L len _ Herr). exact HK'.
+ apply RI_add; [exact HRI| lia| exact Hnb| exact Hun].
Qed.
Lemma step_mmap_none : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "V>'S2'H'K'N':&T1'S?(S7zr4&S<&RH%544321'Q0&Q6r6%211&R:%113'QMvQGvU@vTLr;r:r2%76654321&RLr<%211'B&T8r9%22I1&RG%4231%6231'C'<'UFyR0%211%411&Q3%11E(2%115%:3531'9'>%1299%311&Q4%11I(;%115%C3531%91@&Q5r=%211%71D%I3521&QLv1v0(3%11Q7r8%65542Q>1&T7%123Q;&QK%32Q91&RBvUD(R?r@+Q2%34R72R71rB%73621&UGr1%22Q<1'O(Q9y8%QA11%Q911%Q92QA1%Q511(7(=&UE%12QGQ4%34QGQGR71%53Q?1Q:'M%Q=11%QC2QKS0%Q?11%@6R=;Q?531(Q:&QCr?%211r3r>%?2R51%A4R5R531&Q@%117%E3QO31&QB%11:%H3R261&QD%11=&Q=%11?&Q?%11A&QA%11C&Q>%11E%H8E>;97531'R9%RK11&R6rE%RC2T3T3%R?11%44SB31S=(4(R0%11N%32:1%S63:51'6&RJrJ%24SK1QOT6(@%S<3521&S@r5%211(8%SA3:21&RMrLrD%3321T;rK%T96T8T7T621TCrH&T<rGrC%3221%S35S2S151?'T2vUC(L&R=r7%22@1&QE%12TK?%6231%94S181=p0;1p0B1p0I1p0O1p0Q61tYBU5QC1t[4RNR=1t[BUCS01pXLT<1%A2MF%D4S<C1R>p031p0S81p0SA1p0SD1p0SG1p0SO1p0T61p0T@1p0TL1p0U41p0U81tZ>V2UA1tY@UGUD1tY>UOUI1pQDV11pY4V61pZBV41pZ2V81pZ6V71pZ:V91pZJV;1pQFV=1").
Proof.
intros L pbrk ms mo len ne bb K e h n HK Hq Hlen Hh Hl Hm HRI Hnb HnN Hat HC. subst e.
pose proof (mmap_len_ge len ltac:(lia)) as Hn1. fold n in Hn1.
assert (HnA : n mod page_size = 0) by (unfold n; apply mmap_len_aligned).
assert (Hun : bv_unsigned (Z_to_bv 64 n) = n) by (apply u64_lit; unfold NMAX in HnN; lia).
eapply (bn_mmap_none segs scfg Halloc ms mo len K Hh Hl Hat); [unfold LEN_MAX in Hlen; lia| |].
- change (page_round_up_Z len) with n. eapply (RI_grant_na CAPK CAPB (S ne) bb mo n HRI HCAPK); lia.
- intros a Hg. change (page_round_up_Z len) with n in Hg |- *.
destruct (grant_ok_na_unpack _ _ _ _ Hg) as (G1 & G2 & G3 & G4).
fold h in G3. rewrite (KL2_alloc_top _ _ _ _ _ HK) in G3.
destruct (KL2_mmap_new resv_img img_hi L pbrk h a len true HK Hq Hlen
ltac:(unfold PGSZ; unfold page_size in G1; exact G1) G2 G3 G4) as (HK' & Hans & Herr).
unfold noaccess_model. fold h. apply HC.
+ apply dec_mmap_none_ok; [exact G1| exact G2| exact G3].
+ rewrite answer_ok_mmap. exact Hans.
+ exact Herr.
+ rewrite (event_post_mmap_none L len _ Herr). exact HK'.
+ apply RI_add; [exact HRI| lia| exact Hnb| exact Hun].
Qed.
Lemma dec_mmap_fixed_ok : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "QM'H'UFyR0%211'Cr1&UEr2%2261%53641'B&T7zr3%3221&T<&T;+2+R0%3221+TP0%6221%;291%=291'<'SM%211&SJr4&S;(Q9(;'>'9y8%Q211%311%52Q21%711%72Q4Q4%911(7(=%Q52Q9>%24Q9Q9O1%43615'M%@11':%A2Q>1%C11%E6Q6=;641%I3HG1(4(SH%22N1%QD3N41p0Q21p0QA1pY0QH1pXNQL1").
Proof.
intros addr aw -> Ha. unfold dec_mmap_fixed.
rewrite (mmap_len_of_aligned PGSZ) by (unfold PGSZ; first [lia| reflexivity]).
rewrite !bv_eqb_refl. cbn [andb]. rewrite errno_of_lit by lia. reflexivity.
Qed.
Lemma step_mmap_fixed : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "UG'S2'H'K'N':&T1'Q0&Q6r5%211&SB%113'S?(S7r1&S;&S<&RI%544321'UFyR0%211&UEr2%2241%325:'QMvQGvU@vTLr=r<%6654321H'C'RK&RNr>%211(RDr:%211%83741'<%11F&Q3%11>(2%11J%?3531'9'>%12NN%311&Q4%11H(;%115%H3531%91Q5&Q5%11H%61Q8%M3421&QLv1v0(3%11Q5%55431Q5M&RBvUD(R?z+QB%34Q3QK21rA%73621'O(Q9r9y8%QN11%Q111%Q12QN1%M11(7(=r8%24R3R391%43Q61Q1'M%Q411%Q:2R7RH%Q611%@6?:Q6531(Q:&QC%11R3&Q@%11R5%>4R?R?QME&Q8&QB%11R9&T4%12R:RJ%533R;1%F3QH71&QD%11R?&Q=%11RA&Q?%11RC&QA%11RE&Q>%11RG%G8EC;97531'SM%R>11&SJ%13RLS;S3(4(SH%2261%RM3641'6&RJrG%24S71S4RN(@%S33521&RMrHr?%332S41r3%S@6S?S>S=291rDrCr4%R?5R>R=321'T2vUC(L&R=r6%22>1&QE%12T>E%6231%94RB81<p0;1p0@1p0G1p0N1tYBTGQ71t[4RAR01rB%?2D1%B4RKA1SMp041p0RG1p0S01p0S71p0S=1p0SG1p0SO1p0T91tZFTETA1tY0TFTC1tY>U0TJ1tXLU<U21tY@U8U51pQDU:1pY4U?1pZBU=1pY:UA1pZ6U@1pZ:UB1pZJUD1pQFUF1").
Proof.
intros L pbrk ms mo cur ne bb K h a e aw nw HK Hph Hh Hl Hm HRI Hat HC. subst e aw nw. subst a.
pose proof alloc_ceiling_lt as Hcl.
destruct (KL2_mmap_fixed resv_img img_hi L pbrk h cur HK Hph) as (Ea & Hcal & Hc0 & Hce & Hrf & Hmc & Hans & HK').
rewrite !Ea in Hrf. rewrite !Ea in Hmc. rewrite !Ea in Hans. rewrite !Ea in HK'. rewrite !Ea in Hat. rewrite !Ea in HC. rewrite ?Ea.
set (aw := Z_to_bv 64 cur) in *. set (nw := Z_to_bv 64 PGSZ) in *.
assert (HprP : page_round_up_Z PGSZ = PGSZ) by reflexivity.
eapply (bn_mmap_fixed segs scfg Halloc ms mo cur PGSZ K Hh Hl Hat).
- unfold page_size. unfold PGSZ in Hcal. exact Hcal.
- lia.
- unfold PGSZ; lia.
- rewrite HprP. fold h. rewrite (KL2_alloc_top _ _ _ _ _ HK). lia.
- rewrite HprP. exact Hrf.
- rewrite HprP. exact Hmc.
- rewrite HprP. fold nw. fold aw.
rewrite (fixed_noaccess_model_simple aw nw mo Hl Hm). fold h.
assert (Ua : bv_unsigned aw = cur) by (subst aw; apply u64_lit; unfold PGSZ in *; lia).
assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply u64_lit; unfold PGSZ; lia).
rewrite Ua, Un. apply HC.
+ apply dec_mmap_fixed_ok; [reflexivity| unfold PGSZ in *; lia].
+ unfold answer_ok. change (Z.land MAPFX MAP_FIXED =? 0) with false. exact Hans.
+ exact HK'.
+ eapply RI_tick; [exact HRI| pose proof HRI as (_ & _ & _ & R4 & _); lia].
Qed.
Lemma dec_munmap_ok : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "QI'H'UFyR0%211'Cr2&UEr4%2261%53641&R:%114%62:1%93:81'<'R;%211&R7r6r5(Q9z%@2D1(;'>'9y8%J11%311%52J1%711%72LL%911(7(=r3%24Q1Q1M1%43615'M%@11':%A2Q61%C11%G6E=;641%K3JI1(4(R1(@%211%42Q21%Q>3Q261p0Q61p0Q;1pZFQB1pY0QC1pZ2QG1pXLQH1").
Proof. intros a len aw nw -> ->. unfold dec_munmap. rewrite !bv_eqb_refl. reflexivity. Qed.
Lemma step_munmap : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "V6'S2'H'K'N':&T1'S?(S9r6r4%3221'Q0&Q6r8%211&R:r7%211'UFyR0%211&UEr9%2241r2%4261'QMvQGvU@vTLr?r>%6654321G&RLr@%211&T3'>%12Q5Q5(=r=r<%34Q9Q921&ROrA%211%:3841'E'C%13Q@89&SB%11;%43QC;1%6241'<%11Q3&Q3%11G(2%11Q7%<3531'9%I2Q:Q:%211&Q4%11E(;%115%D3531%81QA&Q5rB%211%71QE%J3521&QLv1v0(3%11QAr;%65542QB1&RBvUD(RArC%221Q:rE%63521'O(Q9z%R72R91y8%R<11%Q211%QK2R<1%O11(7r:%QM4R@R@D1%33Q71Q2'M%Q511%R32RDS4%Q711%@6>9Q7531(Q:&QC%11R>&Q7&Q@%11RA%321R8&Q8&QB%11RE&T4%12OR>%533Q01&QD%11RJ&Q=%11RL&Q?%11RN&QA%11S0&Q>%11S2%G8EA;97531'R;%R>11&R7rFrD%3321S@(4(R1(@%211%42:1%RN3:61'6&RJrK%24SG1S6QG%S33418&RMrL%231R?QKr3%SN6SMSLSK271%R>5R=R<CR2T@'T2vUC(L&R=%129TF&QEr5%221@%6241%94R@81R<p0;1p0=1p0C1p0I1tYBTMQ61t[4R@QO1rG%?21Q5%B4RIA1T:p041p0RF1p0RN1p0S61p0S=1p0SF1p0SN1p0T61p0TB1p0TF1tZFU3TN1tY0U4U11tZ>UHU81tY@U?U<1tY>UEUA1pQDUG1pY4UL1pZBUJ1pZ2UN1pZ0UO1pXLV01pZ6UO1pZ:V11pZJV31pQFV51").
Proof.
intros L pbrk ms mo a l0 len ne bb K e h n aw nw HK Hq Hin Hlen Hh Hl Hm HRI Hat HC. subst e.
pose proof alloc_ceiling_lt as Hcl.
destruct (KL2_munmap resv_img img_hi L pbrk h a l0 len HK Hq Hin Hlen)
as (Hlen1 & Hlen2 & Hal & Ha0 & Hn0 & Hce & Hhas & Hans & HK' & Hcnt & Hlb).
fold n aw nw in Hhas, HK', Hcnt, Hlb, Hlen2, Hn0, Hce.
assert (Hpr : page_round_up_Z len = n) by (rewrite <- Hlen2; reflexivity).
eapply (bn_munmap segs scfg ms mo a len K Hh Hl Hat).
- unfold page_size. unfold PGSZ in Hal. exact Hal.
- lia.
- lia.
- rewrite Hpr. unfold TASK_SIZE. pose_ceil. lia.
- rewrite Hpr. exact Hhas.
- rewrite Hpr. fold aw nw. rewrite (munmap_model_simple aw nw mo Hl Hm). fold h.
assert (Ua : bv_unsigned aw = a) by (subst aw; apply u64_lit; lia).
assert (Un : bv_unsigned nw = n) by (subst nw; apply u64_lit; lia).
rewrite Ua, Un. apply HC.
+ apply dec_munmap_ok; [reflexivity| rewrite Hlen2; reflexivity].
+ exact Hans.
+ exact HK'.
+ eapply RI_remove; [exact HRI| pose proof HRI as (_ & _ & _ & R4 & _); lia].
Qed.
Lemma dec_mprotect_rw_ok : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "QH'H'UFyR0%211'Cr2&UEr3%2261%53641&R:&S;%211%72;1%:3;91'<'R;%211&SKr5(Q9z%@2D1(;'>'9y8%J11%311%52J1%711(7%82MM(=r4%24Q0Q01L%=14%63521'M%@11':%A2Q61%C11%G6E=6741%J3IQ11(4(R1(@%211%42Q11%Q>3Q161p0Q51p0Q;1pZFQB1pY0QC1pXLQG1").
Proof. intros a aw nw -> ->. unfold dec_mprotect_rw, dec_mprotect. rewrite !bv_eqb_refl. reflexivity. Qed.
Lemma step_mprotect : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "V:'S2'H'K'N':&T1'Q0&Q6r7%211&T4&T:+1r5%4221&S;%5221%7291'S?(S8r1&S=%33271'UFyR0%211&UEr2%2241%325>'QMvQGvU@vTLr?r>%6654321G&RLr@%211&T3'>%12Q9Q9%221Q:(=r=r<%34Q>Q>21r;%547Q@21&S0rA%211%=3:41&T7+2%Q>21:%Q>21Q:&SB%11>%6231'C'<%11Q6&Q3%11K(2%11Q:%73531'9%M2Q=Q=%211&Q4%11F(;%115%?3531%81QD&Q5rB%211%71QH%E3521&QLv1v0(3%11QE%55431QEQ:&RBvUD(R@+3%23Q?R>1rE%63521'O(Q9z%R92R;1y8%R>11%Q111%QN2R>1%N11(7r:%QO4RBRBQK1%33Q61Q1'M%Q411%R62RFS;%Q611%@6>95Q631(Q:&QC%11RB&Q@%11RD&Q8&QB%11RG%S@2RGS;%432RH1&QD%11RK&Q=%11RM&Q?%11RO&QA%11S1&Q>%11S3%D8B@;97531'R;%R:11&SK%13S8SKS?(4(R1(@%211%4281%RC3861'6&RJrK%24SE1SBQB%RH3418&RMrL%231SBQFr3%SL6SKSJSI271rFr4%R:5R9R82QO1'T2vUC(L&R=r6%22<1&QE%12THB%6231%94R=81R9p0;1p0?1p0E1p0K1tYBU6Q61t[4R=QL1rG%?21D%B4RFA1T:p041p0RC1p0RK1p0S21p0S91p0SB1p0SK1p0T31p0TB1p0TF1tZFU2TN1tY0U3U01tY>U;U71tXLUMU=1tY@UIUF1pQDUK1pY4V01pZBUN1pYLV21pYNV31pY2V41pZ6V31pZ:V51pZJV71pQFV91").
Proof.
intros L pbrk ms mo b l k ne bb K h a e aw nw HK Hq Hin Hk Hh Hl Hm HRI Hat HC. subst e.
pose proof alloc_ceiling_lt as Hcl.
destruct (KL2_mprotect resv_img img_hi L pbrk h b l k HK Hq Hin Hk) as (Hal & Ha0 & Hce & Hcn & Hcm & Hans & HK').
fold a in Hal, Ha0, Hce, Hcn, Hcm, HK', Hans |- *. fold aw nw in Hcn, Hcm, HK'.
assert (HprP : page_round_up_Z PGSZ = PGSZ) by reflexivity.
eapply (bn_mprotect segs scfg Halloc ms mo a PGSZ K Hh Hl Hat).
- unfold page_size. unfold PGSZ in Hal. exact Hal.
- unfold PGSZ; lia.
- lia.
- rewrite HprP. unfold two_pow_64. lia.
- rewrite HprP. exact Hcn.
- rewrite HprP. exact Hcm.
- rewrite HprP. fold nw. apply RefNodes.mprotect_budget_ok_intro; [exact Hl| exact Hm|].
pose proof (RI_live_limit _ _ _ _ _ HRI HCAPB). pose proof HRI as (_ & _ & _ & R4 & _). unfold vm_live_bytes. fold h. lia.
- rewrite HprP. fold aw nw. unfold mprotect_model. fold h.
assert (Ua : bv_unsigned aw = a) by (subst aw; apply u64_lit; unfold PGSZ in *; lia).
assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply u64_lit; unfold PGSZ; lia).
rewrite Ua, Un. apply HC.
+ apply dec_mprotect_rw_ok; [reflexivity|]. rewrite (mmap_len_of_aligned PGSZ) by (unfold PGSZ; first [lia| reflexivity]). reflexivity.
+ exact Hans.
+ exact HK'.
+ eapply RI_tick; [exact HRI| pose proof HRI as (_ & _ & _ & R4 & _); lia].
Qed.
Lemma ev_step_brk0 : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "O'C&SC'SI'H%3221&SLvQG(S6z%211%5241&SD&SF(R>%116&R4%44>=21'A&SG&SNr1%211%42D1&SEr2%23GF1q091%@5I:H51qZNI1%B5KJJ=1%N3JD1").
Proof. reflexivity. Qed.
Lemma ev_step_brk : forall req, req <> 0 ->
ev_step (EBrk req) =
mbind mget (fun s => mbind (msys (NBrk req) (dec_brk (ps_brk s) req))
(fun a => match a with BrkGrown => mbind (mupd (set_brk_ps req)) (fun _ => mret req) | BrkSame => mret (ps_brk s) end)).
Proof. intros req H. unfold ev_step. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.
Lemma ev_step_mmap_rw : forall len,
ev_step (EMmap 0 len PROT_RW MAPF) =
mbind (msys (NMmap 0 len PROT_RW MAPF) (dec_mmap len [])) (fun a => mret match a with MmErr e => neg_errno e | MmOk x => x end).
Proof. reflexivity. Qed.
Lemma ev_step_mmap_none : forall len,
ev_step (EMmap 0 len PROT_NONE MAPF) =
mbind (msys (NMmap 0 len PROT_NONE MAPF) (dec_mmap_none len [])) (fun a => mret match a with MmErr e => neg_errno e | MmOk x => x end).
Proof. reflexivity. Qed.
Lemma ev_step_mmap_fixed : forall a len,
ev_step (EMmap a len PROT_NONE MAPFX) =
mbind (msys (NMmap a len PROT_NONE MAPFX) (dec_mmap_fixed a len))
(fun x => mret match x with FxKept e => neg_errno e | FxDone => a | FxLost e => neg_errno e end).
Proof. reflexivity. Qed.
Lemma ev_step_munmap : forall a len,
ev_step (EMunmap a len) =
mbind (msys (NMunmap a len) (dec_munmap a len)) (fun x => mret match x with RgErr e => neg_errno e | RgDone _ => 0 end).
Proof. reflexivity. Qed.
Lemma ev_step_mprotect : forall a len prot,
ev_step (EMprotect a len prot) =
mbind (msys (NMprotect a len prot) (dec_mprotect_rw a len)) (fun x => mret match x with RgErr e => neg_errno e | RgDone _ => 0 end).
Proof. reflexivity. Qed.
Lemma machine_event : forall {A B} n (dec : resp -> option A) (f : A -> Monad.M PState B) (s : PState) Qm ms,
implM segs (mbind (msys n dec) f) s Qm ms ->
exists ms1, Exec.msteps segs ms ms1 /\ Nodes.at_node segs n ms1 /\
forall rsp a, dec rsp = Some a -> exists ms2, Exec.msteps segs (nret ms1 rsp) ms2 /\ implM segs (f a) s Qm ms2.
Proof.
intros A B n dec f s Qm ms H. apply implM_bind_inv, implM_msys_inv in H.
destruct H as (ms1 & Hms & Hat & Hk). exists ms1. split; [exact Hms|]. split; [exact Hat|].
intros rsp a E. destruct (Hk rsp a E) as (ms2 & Hms2 & H2). exists ms2. auto.
Qed.
Lemma srz_cj_msteps : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "QH'K'N&T1'Cr3&QE&Q6%113r2%4221%73961'<'UFyR0%211%411&Q3%11=(2%115%A3531'9'>%1299%311&Q4r4%211(;%116%K3631'R<vUDr8r7%43321'T2vUC(L%1265r5%549421r:%521:r6%94=821p051p0<1p0B1p0M1p0Q81pQDQA1pZ8QC1pZ6QD1pZ<QF1pZ:QG1").
Proof.
intros ms ms' mo mo0 K Emo Hh Hl Hms Hc.
eapply srz_msteps; [rewrite Emo, with_vmmaps_halted; exact Hh| rewrite Emo, with_vmmaps_lazy'; exact Hl| apply cj_msteps_cat; exact Hms| exact Hc].
Qed.
Theorem embed : forall {R} (t : M R) L Post (E : ev -> Prop) (ne : nat) (bb : Z) (Q : R -> Prop)
(s : PState) (Qm : R -> PState -> machine_state -> Prop) ms (mo mo0 : Model) K,
ctree_ok L t Post ->
gtree E ne bb t Q ->
(forall a len prot flags, E (EMmap a len prot flags) -> is_fixed flags = false -> mmap_len len <= NMAX) ->
implM segs (membed t) s Qm ms ->
KL L (ps_brk s) (m_vmmaps mo) ->
mo = with_vmmaps (m_vmmaps mo) mo0 ->
m_halted mo0 = None -> m_vm_lazy mo0 = [] -> m_vm_materialized mo0 = [] ->
RI CAPK CAPB ne bb (m_vmmaps mo) ->
(forall r s' ms' mo' L',
Qm r s' ms' -> cpath L t L' r -> Post L' r -> Q r ->
KL L' (ps_brk s') (m_vmmaps mo') ->
mo' = with_vmmaps (m_vmmaps mo') mo0 ->
RI CAPK CAPB 0 0 (m_vmmaps mo') ->
ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
srealizes segs scfg (mkCfg ms' mo') K) ->
srealizes segs scfg (mkCfg ms mo) K.
Proof.
intros R t. induction t as [r|e k IH]; intros L Post E ne bb Q s Qm ms mo mo0 K Hct Hgt HE Himpl HK Emo Hh Hl Hm HRI CONT.
-
cbn [membed] in Himpl. apply implM_ret_inv in Himpl. destruct Himpl as (ms' & Hms & HQ).
eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
cbn [ctree_ok] in Hct. cbn [gtree] in Hgt.
eapply (CONT r s ms' mo L HQ (cpath_ret L r) Hct Hgt HK Emo); try reflexivity.
eapply RI_weaken; [exact HRI| lia| pose proof HRI as (_ & _ & _ & R4 & _); lia].
-
cbn [ctree_ok] in Hct. destruct Hct as [Hpre Hk].
assert (Hne : match e with EUndef _ => False | _ => True end) by (destruct e; cbn in Hpre; auto).
destruct (gtree_vis_inv E ne bb e k Q Hgt Hne) as (ne' & -> & HEe & Hcost & Hg). clear Hgt Hne.
cbn [membed] in Himpl. apply implM_bind_inv in Himpl.
assert (Hh' : m_halted mo = None) by (rewrite Emo, with_vmmaps_halted; exact Hh).
assert (Hl' : m_vm_lazy mo = []) by (rewrite Emo, with_vmmaps_lazy'; exact Hl).
assert (Hm' : m_vm_materialized mo = []) by (rewrite Emo, with_vmmaps_mat; exact Hm).
pose proof HRI as (_ & _ & _ & Hbb0 & _).
assert (KONT : forall z (s1 : PState) ms2 (mo1 : Model) (bb1 : Z),
answer_ok L e z = true -> good e z ->
implM segs (membed (k z)) s1 Qm ms2 ->
KL (event_post L e z) (ps_brk s1) (m_vmmaps mo1) ->
mo1 = with_vmmaps (m_vmmaps mo1) mo0 ->
RI CAPK CAPB ne' bb1 (m_vmmaps mo1) -> 0 <= bb - ecost e <= bb1 ->
ps_m s1 = ps_m s -> ps_fa s1 = ps_fa s -> ps_so s1 = ps_so s ->
srealizes segs scfg (mkCfg ms2 mo1) K).
{ intros z s1 ms2 mo1 bb1 Hans Hgood Hi1 HK1 Emo1 HRI1 Hbb1 E1 E2 E3.
eapply (IH z (event_post L e z) Post E ne' (bb - ecost e) Q s1 Qm ms2 mo1 mo0 K (Hk z Hans) (Hg z Hgood) HE Hi1 HK1 Emo1 Hh Hl Hm).
- eapply RI_weaken; [exact HRI1| lia| lia].
- intros r s' ms' mo' L' HQ' Hcp HP HQr HK' Emo' HRI' E1' E2' E3'.
eapply (CONT r s' ms' mo' L' HQ'); [eapply cpath_vis; [exact Hans| exact Hcp]| exact HP| exact HQr| exact HK'| exact Emo'| exact HRI'| congruence| congruence| congruence]. }
clear IH CONT Hk Hg.
destruct e as [req|a len prot flags|a len|a len prot|p c hh|u]; cbn [event_pre] in Hpre; try contradiction.
+
destruct Hpre as [[-> Hph]|[(cur & Hph & ->)|(b & l & Hph & Hreg & ->)]].
*
rewrite ev_step_brk0 in Himpl. destruct (machine_event _ _ _ _ _ _ Himpl) as (ms1 & Hms & Hat & Hk1).
eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
eapply step_brk0; [exact HK| exact Hph| exact Hh'| exact Hl'| exact Hat|].
intros r0 rsp Hdec Hans HK'.
destruct (Hk1 _ _ Hdec) as (ms2 & Hms2 & Hi2). apply implM_mupd_inv, implM_ret_inv in Hi2.
destruct Hi2 as (ms3 & Hms3 & Hi3).
eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| eapply Exec.msteps_trans; [exact Hms2| exact Hms3]|].
eapply (KONT r0 (set_brk_ps r0 s) ms3 mo bb);
[exact Hans| exact I| exact Hi3| exact HK'| exact Emo| eapply RI_weaken; [exact HRI| lia| lia]| cbn [ecost Z.eqb]; lia
| reflexivity| reflexivity| reflexivity].
*
destruct (KL2_brk_grow1 resv_img img_hi L (ps_brk s) (m_vmmaps mo) cur HK Hph)
as (Ecur & Epbrk & Ereq & Hbal & Hb0 & Hnw & Hsb & Hne0 & HREF & HGR).
rewrite (ev_step_brk _ Hne0) in Himpl. apply implM_mget_inv in Himpl.
rewrite Ereq in *. rewrite <- Epbrk in HREF.
destruct (machine_event _ _ _ _ _ _ Himpl) as (ms1 & Hms & Hat & Hk1).
eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
assert (Hc2 : ecost (EBrk (bv_unsigned (vm_brk (m_vmmaps mo)) + 2 * PGSZ)) = 2 * PGSZ).
{ cbn [ecost]. rewrite (proj2 (Z.eqb_neq _ _) Hne0). reflexivity. }
rewrite Hc2 in *.
eapply (step_brk_grow L (ps_brk s) ms1 mo (2 * PGSZ) ne' bb K HK Hh' Hl' Hm' HRI);
[lia| pose proof NMAX_facts; unfold PGSZ in *; lia| unfold PGSZ, page_size; reflexivity| lia| exact Hbal| exact Hb0| exact Hnw| exact Hsb
| exact HREF| exact HGR| exact Hat| |].
--
intros rsp Hdec Hans HK' HRI'.
destruct (Hk1 _ _ Hdec) as (ms2 & Hms2 & Hi2). apply implM_ret_inv in Hi2. destruct Hi2 as (ms3 & Hms3 & Hi3).
eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| eapply Exec.msteps_trans; [exact Hms2| exact Hms3]|].
eapply (KONT (ps_brk s) s ms3 mo bb);
[exact Hans| exact I| exact Hi3| exact HK'| exact Emo| exact HRI'| lia
| reflexivity| reflexivity| reflexivity].
--
intros rsp h' Hdec Hans HK' HRI'.
destruct (Hk1 _ _ Hdec) as (ms2 & Hms2 & Hi2). apply implM_mupd_inv, implM_ret_inv in Hi2.
destruct Hi2 as (ms3 & Hms3 & Hi3).
eapply (srz_cj_msteps _ ms3 _ mo0); [rewrite Emo, with_vmmaps_twice; reflexivity| exact Hh| exact Hl| eapply Exec.msteps_trans; [exact Hms2| exact Hms3]|].
eapply (KONT _ (set_brk_ps _ s) ms3 _ (bb - 2 * PGSZ));
[exact Hans| exact I| exact Hi3| cbn [ps_brk set_brk_ps]; rewrite with_vmmaps_vm; exact HK'
| rewrite Emo, with_vmmaps_twice, with_vmmaps_vm; reflexivity| rewrite with_vmmaps_vm; exact HRI'| lia
| reflexivity| reflexivity| reflexivity].
*
destruct (KL2_brk_grow2 resv_img img_hi L (ps_brk s) (m_vmmaps mo) b l HK Hph Hreg)
as (Epbrk & Ebrk & Ereq & Hbal & Hb0 & Hnw & Hsb & Hne0 & HREF & HGR).
rewrite (ev_step_brk _ Hne0) in Himpl. apply implM_mget_inv in Himpl.
rewrite Ereq in *. rewrite <- Epbrk in HREF.
assert (Epbrk' : ps_brk s = bv_unsigned (vm_brk (m_vmmaps mo))) by lia.
destruct (machine_event _ _ _ _ _ _ Himpl) as (ms1 & Hms & Hat & Hk1).
eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
assert (Hc2 : ecost (EBrk (bv_unsigned (vm_brk (m_vmmaps mo)) + PGSZ)) = 2 * PGSZ).
{ cbn [ecost]. rewrite (proj2 (Z.eqb_neq _ _) Hne0). reflexivity. }
rewrite Hc2 in *.
eapply (step_brk_grow L (ps_brk s) ms1 mo PGSZ ne' bb K HK Hh' Hl' Hm' HRI);
[unfold PGSZ in *; lia| pose proof NMAX_facts; unfold PGSZ in *; lia| unfold PGSZ, page_size; reflexivity| exact Epbrk'| exact Hbal| exact Hb0| exact Hnw| exact Hsb
| exact HREF| exact HGR| exact Hat| |].
--
intros rsp Hdec Hans HK' HRI'.
destruct (Hk1 _ _ Hdec) as (ms2 & Hms2 & Hi2). apply implM_ret_inv in Hi2. destruct Hi2 as (ms3 & Hms3 & Hi3).
eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| eapply Exec.msteps_trans; [exact Hms2| exact Hms3]|].
eapply (KONT (ps_brk s) s ms3 mo bb);
[exact Hans| exact I| exact Hi3| exact HK'| exact Emo| exact HRI'| unfold PGSZ in *; lia
| reflexivity| reflexivity| reflexivity].
--
intros rsp h' Hdec Hans HK' HRI'.
destruct (Hk1 _ _ Hdec) as (ms2 & Hms2 & Hi2). apply implM_mupd_inv, implM_ret_inv in Hi2.
destruct Hi2 as (ms3 & Hms3 & Hi3).
eapply (srz_cj_msteps _ ms3 _ mo0); [rewrite Emo, with_vmmaps_twice; reflexivity| exact Hh| exact Hl| eapply Exec.msteps_trans; [exact Hms2| exact Hms3]|].
eapply (KONT _ (set_brk_ps _ s) ms3 _ (bb - PGSZ));
[exact Hans| exact I| exact Hi3| cbn [ps_brk set_brk_ps]; rewrite with_vmmaps_vm; exact HK'
| rewrite Emo, with_vmmaps_twice, with_vmmaps_vm; reflexivity| rewrite with_vmmaps_vm; exact HRI'| unfold PGSZ in *; lia
| reflexivity| reflexivity| reflexivity].
+
destruct Hpre as [(Hq & -> & -> & Hprot & Hlen)|(cur & Hph & -> & -> & -> & ->)].
*
assert (Hc2 : ecost (EMmap 0 len prot MAPF) = mmap_len len) by reflexivity. rewrite Hc2 in *.
pose proof (HE 0 len prot MAPF HEe eq_refl) as HnN.
destruct Hprot as [-> | ->].
--
rewrite ev_step_mmap_none in Himpl. destruct (machine_event _ _ _ _ _ _ Himpl) as (ms1 & Hms & Hat & Hk1).
eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
eapply (step_mmap_none L (ps_brk s) ms1 mo len ne' bb K HK Hq Hlen Hh' Hl' Hm' HRI Hcost HnN Hat).
intros aw z rsp h' Hdec Hans Herr HK' HRI'.
destruct (Hk1 _ _ Hdec) as (ms2 & Hms2 & Hi2). apply implM_ret_inv in Hi2. destruct Hi2 as (ms3 & Hms3 & Hi3).
eapply (srz_cj_msteps _ ms3 _ mo0); [rewrite Emo, with_vmmaps_twice; reflexivity| exact Hh| exact Hl| eapply Exec.msteps_trans; [exact Hms2| exact Hms3]|].
eapply (KONT z s ms3 _ (bb - mmap_len len));
[exact Hans| cbn [good]; right; exact Herr| exact Hi3| rewrite with_vmmaps_vm; exact HK'
| rewrite Emo, with_vmmaps_twice, with_vmmaps_vm; reflexivity| rewrite with_vmmaps_vm; exact HRI'| lia
| reflexivity| reflexivity| reflexivity].
--
rewrite ev_step_mmap_rw in Himpl. destruct (machine_event _ _ _ _ _ _ Himpl) as (ms1 & Hms & Hat & Hk1).
eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
eapply (step_mmap_rw L (ps_brk s) ms1 mo len ne' bb K HK Hq Hlen Hh' Hl' Hm' HRI Hcost HnN Hat).
intros aw z rsp h' Hdec Hans Herr HK' HRI'.
destruct (Hk1 _ _ Hdec) as (ms2 & Hms2 & Hi2). apply implM_ret_inv in Hi2. destruct Hi2 as (ms3 & Hms3 & Hi3).
eapply (srz_cj_msteps _ ms3 _ mo0); [rewrite Emo, with_vmmaps_twice; reflexivity| exact Hh| exact Hl| eapply Exec.msteps_trans; [exact Hms2| exact Hms3]|].
eapply (KONT z s ms3 _ (bb - mmap_len len));
[exact Hans| cbn [good]; right; exact Herr| exact Hi3| rewrite with_vmmaps_vm; exact HK'
| rewrite Emo, with_vmmaps_twice, with_vmmaps_vm; reflexivity| rewrite with_vmmaps_vm; exact HRI'| lia
| reflexivity| reflexivity| reflexivity].
*
assert (Hc2 : ecost (EMmap (round_up_pg cur) PGSZ PROT_NONE MAPFX) = 0) by reflexivity. rewrite Hc2 in *.
rewrite ev_step_mmap_fixed in Himpl. destruct (machine_event _ _ _ _ _ _ Himpl) as (ms1 & Hms & Hat & Hk1).
eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
eapply (step_mmap_fixed L (ps_brk s) ms1 mo cur ne' bb K HK Hph Hh' Hl' Hm' HRI Hat).
intros rsp h' Hdec Hans HK' HRI'.
destruct (Hk1 _ _ Hdec) as (ms2 & Hms2 & Hi2). apply implM_ret_inv in Hi2. destruct Hi2 as (ms3 & Hms3 & Hi3).
eapply (srz_cj_msteps _ ms3 _ mo0); [rewrite Emo, with_vmmaps_twice; reflexivity| exact Hh| exact Hl| eapply Exec.msteps_trans; [exact Hms2| exact Hms3]|].
eapply (KONT (round_up_pg cur) s ms3 _ bb);
[exact Hans| cbn [good]; left; reflexivity| exact Hi3| rewrite with_vmmaps_vm; exact HK'
| rewrite Emo, with_vmmaps_twice, with_vmmaps_vm; reflexivity| rewrite with_vmmaps_vm; exact HRI'| lia
| reflexivity| reflexivity| reflexivity].
+
destruct Hpre as (Hq & l0 & Hin & Hlen).
assert (Hc2 : ecost (EMunmap a len) = 0) by reflexivity. rewrite Hc2 in *.
rewrite ev_step_munmap in Himpl. destruct (machine_event _ _ _ _ _ _ Himpl) as (ms1 & Hms & Hat & Hk1).
eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
eapply (step_munmap L (ps_brk s) ms1 mo a l0 len ne' bb K HK Hq Hin Hlen Hh' Hl' Hm' HRI Hat).
intros rsp h' Hdec Hans HK' HRI'.
destruct (Hk1 _ _ Hdec) as (ms2 & Hms2 & Hi2). apply implM_ret_inv in Hi2. destruct Hi2 as (ms3 & Hms3 & Hi3).
eapply (srz_cj_msteps _ ms3 _ mo0); [rewrite Emo, with_vmmaps_twice; reflexivity| exact Hh| exact Hl| eapply Exec.msteps_trans; [exact Hms2| exact Hms3]|].
eapply (KONT 0 s ms3 _ bb);
[exact Hans| reflexivity| exact Hi3| rewrite with_vmmaps_vm; exact HK'
| rewrite Emo, with_vmmaps_twice, with_vmmaps_vm; reflexivity| rewrite with_vmmaps_vm; exact HRI'| lia
| reflexivity| reflexivity| reflexivity].
+
destruct Hpre as (Hq & -> & -> & b & l & kk & Hin & -> & Hk2).
assert (Hc2 : ecost (EMprotect (b + (1 + kk) * PGSZ) PGSZ PROT_RW) = 0) by reflexivity. rewrite Hc2 in *.
rewrite ev_step_mprotect in Himpl. destruct (machine_event _ _ _ _ _ _ Himpl) as (ms1 & Hms & Hat & Hk1).
eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
eapply (step_mprotect L (ps_brk s) ms1 mo b l kk ne' bb K HK Hq Hin Hk2 Hh' Hl' Hm' HRI Hat).
intros rsp h' Hdec Hans HK' HRI'.
destruct (Hk1 _ _ Hdec) as (ms2 & Hms2 & Hi2). apply implM_ret_inv in Hi2. destruct Hi2 as (ms3 & Hms3 & Hi3).
eapply (srz_cj_msteps _ ms3 _ mo0); [rewrite Emo, with_vmmaps_twice; reflexivity| exact Hh| exact Hl| eapply Exec.msteps_trans; [exact Hms2| exact Hms3]|].
eapply (KONT 0 s ms3 _ bb);
[exact Hans| reflexivity| exact Hi3| rewrite with_vmmaps_vm; exact HK'
| rewrite Emo, with_vmmaps_twice, with_vmmaps_vm; reflexivity| rewrite with_vmmaps_vm; exact HRI'| lia
| reflexivity| reflexivity| reflexivity].
Qed.
Definition vm_shrunk (h0 h : VmMaps) : Prop :=
vm_reserved h = vm_reserved h0
/\ (length (vm_maps h) <= length (vm_maps h0))%nat
/\ live_bytes (vm_maps h) <= live_bytes (vm_maps h0)
/\ (Forall (fun p => bv_unsigned (snd p) <= NMAX) (vm_maps h0) -> Forall (fun p => bv_unsigned (snd p) <= NMAX) (vm_maps h))
/\ vm_limit h = vm_limit h0 /\ vm_mmap_base h = vm_mmap_base h0.
Lemma vm_shrunk_refl : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "5'Q0&QJr1%2211pY@41").
Proof. intros h. unfold vm_shrunk. repeat split; auto; lia. Qed.
Lemma vm_shrunk_remove : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "Q6'Q0'UFyR0%211'9'>%1233%311&QJr6r5%3221r7(Q:&QC%116&Q7&Q@%119%3219r4r3r2&Q?%11?&QA%11A&Q>%11C%@8>:987531%F2B1p0D1pY8M1p[6N1pZ@K1pY0Q01pY@Q41pYDQ51").
Proof.
intros h0 h aw na sb br (S1 & S2 & S3 & S4 & S5 & S6). unfold vm_shrunk. cbn [vm_reserved vm_maps vm_limit vm_mmap_base vm_init_sp].
pose proof (RefNodes.live_bytes_map_remove_le (vm_maps h) aw) as Hlb.
unfold map_remove in *. pose proof (length_filter_le (fun p : word * word => negb (bv_eqb (fst p) aw)) (vm_maps h)) as Hlen.
splits; auto; try lia. intros HF. apply Forall_filter. apply S4. exact HF.
Qed.
Lemma step_munmap_free : ltac2:(TCodec.tc2 tcn__CJ_Bridge_Embed "UH'S2'H'K'N&T1'S?(S9r4r2%3221'Q0&Q6r6%211&R:r5%211'UFyR0%211&UEr7%2241%325?'QMvQGvU@vTLr=r<%6654321G&RLr>%211&T3'>%12Q3Q3(=r;r:%34Q7Q721&ROr?%211%:3841'E'C%13Q>89&SB%11;%43QA;1%6241'<%11Q2&Q3%11G(2%11Q6%<3531'9%I2Q9Q9%211&Q4%11E(;%115%D3531%81Q@&Q5r@%211%71QD%J3521&RBvUD(RA%127Q<rB%53421'O(Q9z%QN2R01y8%R311%J11%QC2R31%G11(7r9%QE4R7R7QC1%33O1J'M%M11':%QL2R<1%Q011%A6?:Q0641(Q:&QC%11R8&Q7&Q@%11R;%321R2&Q8&QB%11R?&T4%12Q0R@%533Q11&QD%11RD&Q=%11RF&Q?%11RH&QA%11RJ&Q>%11RL%G8EA;97531'R;%R711&R7rCrA%3321SG(4(R1(@%211%42:1%RG3:61'6&RJrH%24S@1R4QH%RL3418&RMrI%231?QLr3%SG6SFSESD271'T2vUC(L&R=%12<T5&QErG%22T@1%6241%94R?81Lp0;1p0A1p0G1tYBTCQ41t[4R?QM1rD%>21Q3%A4RG@1SGp041p0RE1p0RL1p0S31p0S<1p0SD1p0SL1p0T81p0T<1tZFTHTD1tY0TITF1tZ>U<TM1tY@U4U11tY>U:U61pQDU<1pZ2U@1pZ0UA1pXLUB1pZ6UA1pZ:UC1pZJUE1pQFUG1").
Proof.
intros L pbrk ms mo a l0 len K e h n aw nw HK Hq Hin Hlen Hh Hl Hm Hat HC. subst e.
pose proof alloc_ceiling_lt as Hcl.
destruct (KL2_munmap resv_img img_hi L pbrk h a l0 len HK Hq Hin Hlen)
as (Hlen1 & Hlen2 & Hal & Ha0 & Hn0 & Hce & Hhas & Hans & HK' & Hcnt & Hlb).
fold n aw nw in Hhas, HK', Hcnt, Hlb, Hlen2, Hn0, Hce.
assert (Hpr : page_round_up_Z len = n) by (rewrite <- Hlen2; reflexivity).
eapply (bn_munmap segs scfg ms mo a len K Hh Hl Hat).
- unfold page_size. unfold PGSZ in Hal. exact Hal.
- lia.
- lia.
- rewrite Hpr. unfold TASK_SIZE. pose_ceil. lia.
- rewrite Hpr. exact Hhas.
- rewrite Hpr. fold aw nw. rewrite (munmap_model_simple aw nw mo Hl Hm). fold h.
assert (Ua : bv_unsigned aw = a) by (subst aw; apply u64_lit; lia).
assert (Un : bv_unsigned nw = n) by (subst nw; apply u64_lit; lia).
rewrite Ua, Un. apply HC.
+ apply dec_munmap_ok; [reflexivity| rewrite Hlen2; reflexivity].
+ exact Hans.
+ exact HK'.
Qed.
Theorem embed_free : forall {R} (t : M R) L Post (ne : nat) (bb : Z) (Q : R -> Prop)
(s : PState) (Qm : R -> PState -> machine_state -> Prop) ms (mo mo0 : Model) (h0 : VmMaps) K,
ctree_ok L t Post ->
gtree efree_ok ne bb t Q ->
implM segs (membed t) s Qm ms ->
KL L (ps_brk s) (m_vmmaps mo) ->
mo = with_vmmaps (m_vmmaps mo) mo0 ->
m_halted mo0 = None -> m_vm_lazy mo0 = [] -> m_vm_materialized mo0 = [] ->
vm_shrunk h0 (m_vmmaps mo) ->
(forall r s' ms' mo' L',
Qm r s' ms' -> cpath L t L' r -> Post L' r -> Q r ->
KL L' (ps_brk s') (m_vmmaps mo') ->
mo' = with_vmmaps (m_vmmaps mo') mo0 ->
vm_shrunk h0 (m_vmmaps mo') ->
ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
srealizes segs scfg (mkCfg ms' mo') K) ->
srealizes segs scfg (mkCfg ms mo) K.
Proof.
intros R t. induction t as [r|e k IH]; intros L Post ne bb Q s Qm ms mo mo0 h0 K Hct Hgt Himpl HK Emo Hh Hl Hm HS CONT.
- cbn [membed] in Himpl. apply implM_ret_inv in Himpl. destruct Himpl as (ms' & Hms & HQ).
eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
cbn [ctree_ok] in Hct. cbn [gtree] in Hgt.
eapply (CONT r s ms' mo L HQ (cpath_ret L r) Hct Hgt HK Emo HS); reflexivity.
- cbn [ctree_ok] in Hct. destruct Hct as [Hpre Hk].
assert (Hne : match e with EUndef _ => False | _ => True end) by (destruct e; cbn in Hpre; auto).
destruct (gtree_vis_inv efree_ok ne bb e k Q Hgt Hne) as (ne' & -> & HEe & Hcost & Hg). clear Hgt Hne.
cbn [membed] in Himpl. apply implM_bind_inv in Himpl.
assert (Hh' : m_halted mo = None) by (rewrite Emo, with_vmmaps_halted; exact Hh).
assert (Hl' : m_vm_lazy mo = []) by (rewrite Emo, with_vmmaps_lazy'; exact Hl).
assert (Hm' : m_vm_materialized mo = []) by (rewrite Emo, with_vmmaps_mat; exact Hm).
destruct e as [req|a len prot flags|a len|a len prot|p c hh|u]; cbn [efree_ok] in HEe; try contradiction.
cbn [event_pre] in Hpre. destruct Hpre as (Hq & l0 & Hin & Hlen).
rewrite ev_step_munmap in Himpl. destruct (machine_event _ _ _ _ _ _ Himpl) as (ms1 & Hms & Hat & Hk1).
eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
eapply (step_munmap_free L (ps_brk s) ms1 mo a l0 len K HK Hq Hin Hlen Hh' Hl' Hm' Hat).
intros rsp h' Hdec Hans HK'.
destruct (Hk1 _ _ Hdec) as (ms2 & Hms2 & Hi2). apply implM_ret_inv in Hi2. destruct Hi2 as (ms3 & Hms3 & Hi3).
eapply (srz_cj_msteps _ ms3 _ mo0); [rewrite Emo, with_vmmaps_twice; reflexivity| exact Hh| exact Hl| eapply Exec.msteps_trans; [exact Hms2| exact Hms3]|].
eapply (IH 0 (event_post L (EMunmap a len) 0) Post ne' (bb - ecost (EMunmap a len)) Q s Qm ms3 _ mo0 h0 K
(Hk 0 Hans) (Hg 0 eq_refl) Hi3).
+ rewrite with_vmmaps_vm. exact HK'.
+ rewrite Emo, with_vmmaps_twice, with_vmmaps_vm. reflexivity.
+ exact Hh. + exact Hl. + exact Hm.
+ rewrite with_vmmaps_vm. apply vm_shrunk_remove. exact HS.
+ intros r s' ms' mo' L' HQ' Hcp HP HQr HK'' Emo' HS' E1 E2 E3.
eapply (CONT r s' ms' mo' L' HQ'); [eapply cpath_vis; [exact Hans| exact Hcp]| exact HP| exact HQr| exact HK''| exact Emo'| exact HS'| exact E1| exact E2| exact E3].
Qed.
End EVENTS.
End CEIL_WRAP_1.
