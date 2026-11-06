From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO0g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract Img0 FrameAPI SlotPack AllocPack AllocPackRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import Ledger PjStruct ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import
pj_parse_c check_no_overread_c check_reject_clean_starved_c round_trip_text_c check_round_trip_c EntryDefs
LLVMFuzzerTestOneInput_c EntrySR Statement.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PackFit PackOwn PackVec PackBand PackBig.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require PackRooms PackFold.
Import ListNotations.
Local Open Scope Z_scope.

Definition CS_pre (pl : list byte) : list Z := CS_of (beta2_x (zb pl)).

Lemma CS_pre_ok : CS_ok CS_pre.
Proof.
  intros pl. split; [apply CS_of_len|]. intros k Hk. unfold CS_pre. rewrite CS_of_nth by exact Hk.
  pose proof (proj1 (beta2_x_own (zb pl)) k). unfold PCAP0. lia.
Qed.

Lemma zsum_nn : forall (f : Z -> Z) l, (forall i, In i l -> 0 <= f i) -> 0 <= zsumZ f l.
Proof.
  intros f l H. induction l as [|a l IH]; [cbn; lia|]. rewrite PackReparse.zsumZ_cons.
  pose proof (H a (or_introl eq_refl)).
  assert (0 <= zsumZ f l) by (apply IH; intros i Hi; apply H; right; exact Hi). lia.
Qed.

Lemma le_zsum : forall (f : Z -> Z) l k, (forall i, In i l -> 0 <= f i) -> In k l -> f k <= zsumZ f l.
Proof.
  intros f l k H Hk. induction l as [|a l IH]; [destruct Hk|]. rewrite PackReparse.zsumZ_cons.
  destruct Hk as [<-|Hk].
  - pose proof (zsum_nn f l ltac:(intros i Hi; apply H; right; exact Hi)). lia.
  - pose proof (H a (or_introl eq_refl)).
    assert (f k <= zsumZ f l) by (apply IH; [intros i Hi; apply H; right; exact Hi | exact Hk]). lia.
Qed.

Lemma drv_live_le2 : forall d, drv_pb d -> forall k, 0 <= k < 49 -> znth k (pb_live d) <= 2.
Proof.
  intros d (HL & HN & HS & _) k Hk.
  assert (Hin : In k (zseq 0 49)) by (apply In_zseq; lia).
  pose proof (le_zsum (fun i => znth i (pb_live d)) (zseq 0 49) k ltac:(intros i Hi; apply HN; apply In_zseq in Hi; lia) Hin).
  unfold PDRV_LIVE in HS. cbv beta in *. lia.
Qed.

Theorem slot_contract_of_entry :
  (forall (rc : RunCeil) (fx : FPState) (B : malloc_syms) (API : AllocAPI B) (SH : sink_head) (SK : sink_syms)
          (ra empty stk : Z),
     (forall fx' : FPState, @frame_allocator rc fx' B API) ->
     @entry_sr_contract fx rc B API SH SK pack_form ra empty stk) ->
  slot_contract.
Proof.
  intros HE. exists CS_pre. split; [exact CS_pre_ok|].
  intros rc fx LS B API SH SK ra empty stk Hsy Hgl Hsk HFA Hsh Hra Hemp Hemp2 Hstk j Hj.
  intros L A regs mem md p n pl b K Hpre Hres Hent HGI HR Hro Hsp Hfrm HK.
  destruct Hsh as [HLIBK _]. rewrite HLIBK.
  destruct (omx_GI_ledger B j mem L A HGI) as (peak & cnt & Hled & Hcnt).
  destruct Hent as (Hlc & Hcap & d & Hd & Elive & Ebytes).
  cbn [TDP fold_left] in Elive, Ebytes.
  pose proof Hres as Hres'.
  destruct Hres' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLL & _).
  set (b0 := PB (pb_live b) (pb_bytes b) (CS_pre pl)).
  assert (Hres0 : res_ok_pack A b0).
  { apply res_ok_pack_raise; [exact Hres | apply CS_of_len | intros k Hk; exact (proj2 (Hcap k Hk))]. }
  assert (HL0 : length (pb_live b0) = 49%nat) by exact HLL.
  assert (HCNT : 0 <= cnt <= 3 * 2 ^ 60) by (destruct Hcnt as [H1 H2]; split; [exact H1|]; lia).
  assert (Hrooms : entry_rooms pack_form b0 cnt pl).
  { intros Hn.
    assert (Hlen : Z.of_nat (length (zb pl)) <= pf_MAX)
      by (unfold zb; rewrite length_map; unfold ent_n in Hn; unfold pf_MAX; lia).
    apply (PackRooms.rooms b0 (beta2_x (zb pl))); try exact Hn; try exact eq_refl; try exact HCNT; try exact HL0.
    - intros k Hk. cbn [pb_live b0]. rewrite Elive. exact (drv_live_le2 d Hd k Hk).
    - cbn [pb_bytes b0]. rewrite Ebytes. destruct Hd as (_ & _ & _ & HB). unfold PDRV_BYTES in HB. lia.
    - intros k Hk. cbn [pb_cap b0]. unfold CS_pre. apply CS_of_nth, Hk.
    - cbn [pb_cap b0]. exact (pack_big_fit (zb pl) Hlen). }
  pose proof (HE rc fx B API SH SK ra empty stk HFA Hsy Hgl Hsk Hra Hemp2 Hemp Hstk j L A regs mem md p n pl peak cnt b0
                 Hj Hpre HR Hro Hsp Hfrm Hled (proj2 Hcnt) Hres0 Hrooms) as HSR.
  apply (SR_realizes _ _ _ _ HSR).
  intros c' (fx' & L' & A' & regs' & mem' & md' & E1 & E2 & E3 & Dp & cset & b4 & trs & Ds & Df &
             Ec & Hf & Hpost & HGI' & Hwit & Hok).
  rewrite (PackFold.entry_fold_pack b0 cnt pl E1 E2 E3 Dp cset b4 trs Ds Df HL0 HCNT Hwit) in Hok.
  apply HK. exists fx', L', A', regs', mem', md'. split; [exact Ec|]. split; [exact Hf|]. split; [|exact HGI'].
  destruct Hpost as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17 & Q18 & Q19).
  unfold lib_post_pg.
  exact (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj Q6 (conj Q7 (conj Q8 (conj Q9 (conj Q10 (conj Q11 (conj Q12
          (conj Q13 (conj Q14 (conj Q15 (conj Q16 (conj Q17 (conj Q18 (conj Hok Q19))))))))))))))))))).
Qed.
