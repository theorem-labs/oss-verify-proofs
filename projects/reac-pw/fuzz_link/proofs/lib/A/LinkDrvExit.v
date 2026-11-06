From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK00 YP0m YP09 YI04 YG00 YG01 YG0f YG0n YG0d YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YP08.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AD2f AD1u AD1w AMemFileSink AMemFile.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* The exit leaf over the loop state's image regions IMG_L, where ofl_head [OFL_LO, OFL_HI) is clipped out of the
   region R_A8 (AD2f.v), split by the kept list: with nothing kept the heads are 0, ofl_head holds image bytes again,
   and the released walk at IMG_L0 applies (exit_leaf0_tfa); with the FILE kept, the walk that visits it
   (exit_file_tfa). *)

(* R_A8's first piece in IMG_L0, and its two pieces in IMG_L around ofl_head. *)
Definition R_OFL0 : YP09.region := YP09.mkRegion None 0x6522c0 0x652318 0 0 [YP09.mkChunk 0x6522c0 (CImg 88)].
Definition R_OFL1 : YP09.region := YP09.mkRegion None 0x6522c0 0x652308 0 0 [YP09.mkChunk 0x6522c0 (CImg 72)].
Definition R_OFL2 : YP09.region := YP09.mkRegion None 0x652310 0x652318 0 0 [YP09.mkChunk 0x652310 (CImg 8)].
Lemma IMG_L_split : IMG_L0 = firstn 66 IMG_L0 ++ R_OFL0 :: skipn 67 IMG_L0 /\
  IMG_L = firstn 66 IMG_L0 ++ R_OFL1 :: R_OFL2 :: skipn 67 IMG_L0.
Proof. vm_compute. split; reflexivity. Qed.

(* ofl_head is .bss: its image bytes are 0. *)
Lemma ofl_img_zero : forall a, OFL_LO <= a < OFL_HI -> img_byte tfibsegs a = Some (Z_to_bv 8 0).
Proof.
intros a Ha. unfold OFL_LO, OFL_HI in Ha.
assert (Hc : exists k, (k < 8)%nat /\ a = 0x652308 + Z.of_nat k) by (exists (Z.to_nat (a - 0x652308)); split; lia).
destruct Hc as (k & Hk & ->). do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma region_ok_ofl0 : forall E m, region_ok tfibsegs E m R_OFL1 -> region_ok tfibsegs E m R_OFL2 ->
  val_mem tfibsegs m OFL_LO 8 0 -> region_ok tfibsegs E m R_OFL0.
Proof.
intros E m (_ & _ & _ & C1) (_ & _ & _ & C2) Hv.
apply Forall_inv in C1. apply Forall_inv in C2.
unfold region_ok. cbn [R_OFL0 YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
intros i Hi. cbn [c_len cv_len YP09.c_val] in Hi.
destruct (Z.lt_ge_cases i 72) as [H1|H1].
- destruct (C1 i ltac:(cbn [c_len cv_len YP09.c_val]; lia)) as (b & Hb1 & Hb2).
  exists b. cbn [cbyte YP09.c_off YP09.c_val] in Hb1, Hb2 |- *. split; assumption.
- destruct (Z.lt_ge_cases i 80) as [H2|H2].
  + exists (Z_to_bv 8 0). cbn [cbyte YP09.c_off YP09.c_val].
    replace (0 + 0x6522c0 + i) with (OFL_LO + Z.of_nat (Z.to_nat (i - 72))) by (unfold OFL_LO; lia).
    split; [apply ofl_img_zero; unfold OFL_LO, OFL_HI; lia|].
    rewrite (Hv (Z.to_nat (i - 72)) ltac:(lia)). f_equal. f_equal. apply amf_le_byte_0.
  + destruct (C2 (i - 80) ltac:(cbn [c_len cv_len YP09.c_val]; lia)) as (b & Hb1 & Hb2).
    exists b. cbn [cbyte YP09.c_off YP09.c_val] in Hb1, Hb2 |- *.
    replace (0 + 0x6522c0 + i) with (0 + 0x652310 + (i - 80)) by lia. split; assumption.
Qed.

(* Image regions without a base are pairwise disjoint when their ranges are (YP08.v img_pairwise). *)
Lemma pd_none_sound : forall E rs,
  forallb (fun r => match YP09.r_base r with None => true | Some _ => false end) rs = true ->
  YP08.img_pairwise rs = true -> pairwise_disjoint E rs.
Proof.
intros E. induction rs as [|r rs IH]; intros Hb H; [exact I|].
cbn [forallb] in Hb. cbn [YP08.img_pairwise] in H. cbn [pairwise_disjoint].
apply andb_prop in Hb as [Hr Hb]. apply andb_prop in H as [Hd H].
split; [|apply IH; assumption].
assert (Er : YP09.r_base r = None) by (destruct (YP09.r_base r); [discriminate|reflexivity]).
clear IH H Hr. induction rs as [|r' rs IH']; cbn [all_disjoint]; [exact I|].
cbn [forallb] in Hd, Hb. apply andb_prop in Hd as [Hrr' Hd]. apply andb_prop in Hb as [Hr' Hb].
split; [|apply IH'; assumption].
assert (Er' : YP09.r_base r' = None) by (destruct (YP09.r_base r'); [discriminate|reflexivity]).
unfold extent_disjoint. rewrite Er, Er'. cbn [base_val]. unfold YP08.img_disjoint in Hrr'.
apply orb_prop in Hrr' as [X|X]; apply Z.leb_le in X; lia.
Qed.

(* With ofl_head's image bytes back in memory, the loop state's regions give the released exit walk's. *)
Lemma mem_ok_L0_of_L : forall E m, mem_ok tfibsegs E m IMG_L -> val_mem tfibsegs m OFL_LO 8 0 -> mem_ok tfibsegs E m IMG_L0.
Proof.
intros E m (_ & Hok & _) Hv. destruct IMG_L_split as [E0 E1].
split; [vm_compute; reflexivity|]. split.
- rewrite E0. rewrite E1 in Hok. apply Forall_app in Hok as [HA HC].
  apply Forall_inv_tail in HC as HC1. apply Forall_inv in HC as H1.
  apply Forall_inv_tail in HC1 as HC2. apply Forall_inv in HC1 as H2.
  apply Forall_app. split; [exact HA|]. apply Forall_cons; [exact (region_ok_ofl0 E m H1 H2 Hv) | exact HC2].
- apply pd_none_sound; vm_compute; reflexivity.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Lemma tfib_exit_leafT : exit_leaf0_tfa B xst -> exit_file_tfa B xst -> exit_leaf_tfa B xst.
Proof.
intros L0 LF E' W regs mem md ly S usp fs code k T E0 U U16 Htid Ra0 Hc Hsp R3 R4 HM Hwin HAI HAR HTOP Hnev HSO Hfds Hfs HFI Hinc.
pose proof HFI as (HG & _ & _ & _).
destruct HG as [(Hh0 & ->) | (f & _ & -> & _)].
- apply (L0 E' W regs mem md ly S usp fs code k E0 U U16 Htid Ra0 Hc Hsp R3 R4); try assumption.
  apply mem_ok_L0_of_L; [exact HM|].
  pose proof (amf_heads_ofl tfibsegs link_amf _ 0 Hh0) as X. exact X.
- apply (LF E' W regs mem md ly S usp fs code k f E0 U U16 Htid Ra0 Hc Hsp R3 R4 HM Hwin HAI HAR HTOP Hnev HSO Hfds Hfs HFI).
  apply Hinc. left. reflexivity.
Qed.
End c.
