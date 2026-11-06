(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import SumsLib Sums_code.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list37Corelib7Numbers7BinNumshe4Npos35stdpp9bitvectorbdefinitionsje2bv04cons03nil69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9Sums_code~~~~~~mb7W_a2278mb7W_a227cmb7W_a2280mb7W_a2284mb7W_a2288mb7W_a228cmb7W_a2290mb7W_a2294mb7W_a2298mb7W_a229cmb7W_a22a0mb7W_a22a4mb7W_a22a8mb7W_a22acmb7W_a22b0mb7W_a22b4mb7W_a22b8mb7W_a22bcmb7W_a22c0mb7W_a22c4mb7W_a22c8mb7W_a22ccmb7W_a22d0mb7W_a22d437Corelib4Init5Logichp71Ije2BVje4BvWfhe1Z46Stdlib6ZArith6BinInt1Zhs04landhs03lorjebbv_unsignedhs02lehp73andhs02lt79OSSVerify6Proofsaboost_jsonafuzz_parse3libbBothIMemset4FPX1~~~~~~ig87align15hp72eq69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~ilc6v_andiilc4v_orhs03powje7Z_to_bvhs06modulo69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7SumsLib~~~~~~is42M8hs03mul37Corelib5Lists7ListDefjgb6repeat3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsjich0word_to_le_bytesig86cbyte_ig85cpat_ilc4getr3h5LinuxProcessSemantics5Riscv7Preludejp35bvmap69OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Hoare~~~~~~js23at_69OSSVerify6Proofsaboost_jsonafuzz_parse3libbBothIMemset~~~~~~kg16cbyte_ilc4mkstis45msetkhs03sub03nathp72exkg1cimemset_clob69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6CatSim~~~~~~knc6mstepsjs2aregs_agreejs26ret_ok36Stdlib5Lists4Listkt72Inhs06of_natkg15cpat_hs03add69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~lga6wbyteshs06to_nat79OSSVerify6Proofsaboost_jsonafuzz_parse3libbBothIMemset4FPX2~~~~~~ll8h2asan_imemset_entrykg1dimemset_wordsis47code_at69OSSVerifyaboost_jsonafuzz_parse6images9AsanUbsan1M~~~~~~lsefloaded_segments06option04bool04truehp73notjic8store_okkg17align153h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypemkd7Segment" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition imemset_words : ltac2:(zQ "30!h8!j7!lb@1$0@1$2@1$1#i0") := ltac2:(zQ "hc0!j7!lb!m0!m6!q7!r1!rb!s5!sf!t9!u3!ud!v7!hg1!hgb!hh5!hhf!hi9!hj3!hjd!hk7!hl1!hlb!hm5!hmf!hn9!ho3!hod@3$2@1$1@1$0#i0$4@3$2@1$1@1$0#i0$5@3$2@1$1@1$0#i0$6@3$2@1$1@1$0#i0$7@3$2@1$1@1$0#i0$8@3$2@1$1@1$0#i0$9@3$2@1$1@1$0#i0$a@3$2@1$1@1$0#i0$b@3$2@1$1@1$0#i0$c@3$2@1$1@1$0#i0$d@3$2@1$1@1$0#i0$e@3$2@1$1@1$0#i0$f@3$2@1$1@1$0#i0$h0@3$2@1$1@1$0#i0$h1@3$2@1$1@1$0#i0$h2@3$2@1$1@1$0#i0$h3@3$2@1$1@1$0#i0$h4@3$2@1$1@1$0#i0$h5@3$2@1$1@1$0#i0$h6@3$2@1$1@1$0#i0$h7@3$2@1$1@1$0#i0$h8@3$2@1$1@1$0#i0$h9@3$2@1$1@1$0#i0$ha@3$2@1$1@1$0#i0$hb@1$3@1$1@1$0#i0").

(* [comment removed for export] *)
Definition imemset_clob : ltac2:(zQ "30!h8!j7!lb@1$0@1$2@1$1#5") := ltac2:(zQ "70!j7!lb!m0!hqb!hr0!hr5!m6@3$2@1$1@1$0#5@3$4@1$0#5+bKv$3@2$5@1$0#5+b@3$2@1$1@1$0#5@3$4@1$0#5+cKv$3@2$5@1$0#5+c@3$2@1$1@1$0#5@3$4@1$0#5+dKv$3@2$5@1$0#5+d@1$6@1$1@1$0#5").

(* [comment removed for export] *)
Definition align15 : ltac2:(zQ "30!hrc!j7!lb>1n$0>1s@1$2@1$1#k0$0") := ltac2:(zQ "60!j7!hrc!ht8!hu0!lb!hu7\1n$1\1s@1$4@1$0#k0@2$2@2$3^2@2$5@1$0#k0^1+f").

Lemma land15_range : ltac2:(zQ "50!ht8!hv5!hvb!hrc!ig2>1x$3>0@2$1Z^1@2$2@2$1Z@2$0^2+f@2$4@2$0^2+f+h0").
Proof.
  intros x Hx. change 15%Z with (Z.ones 4). rewrite Z.land_ones by lia.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma align15_range : ltac2:(zQ "70!ikb!hv5!hvb!j7!hrc!ig2!lb>1n$4>1s@1$6@1$3#k0>0@2$1Z^2@2$2@2$1Z@2$0^3^2@2$5@2$0^3^2+h0").
Proof.
  intros n s Hn. unfold align15. apply land15_range. apply Z.lor_nonneg. pose proof (u64_range s). lia.
Qed.

Lemma u_align15 : ltac2:(zQ "d0!j7!hrc!hvb!il6!ikb!ip7!iq1!hv5!ig2!iq9!ir0!lb!hu7>1n$1>1s@1$b@1$0#k0>0@2$2@2$7Z^2@2$8^2@2$9+2+k0@3$3$1@2$c@1$0#k0@2$5@2$6@2$a@1$0#k0^3^2+f@2$4^3^2").
Proof.
  intros n s Hn. pose proof (u64_range s) as Hs.
  pose proof (Z_lor_range n (bv_unsigned s) Hn Hs) as Hl.
  unfold v_andi, v_or, align15. rewrite (u_Z2bv n) by lia.
  rewrite (u_Z2bv (Z.lor n (bv_unsigned s))) by lia.
  change (bv_wrap 64 15) with 15%Z.
  pose proof (land15_range (Z.lor n (bv_unsigned s)) ltac:(lia)).
  apply u_Z2bv; lia.
Qed.

Lemma align15_n16 : ltac2:(zQ "70!hrc!il6!j7!ikb!hv5!ira!lb>1n$0>1s@1$6@1$2#k0>0@2$4Z^2>0@3$1$0@2$3^3^2Z@3$1$0@2$5^4+h0Z").
Proof.
  intros n s Hn H. unfold align15 in H. pose proof (u64_range s).
  rewrite Z.land_lor_distr_l in H. apply Z.lor_eq_0_iff in H as [H _].
  change 15%Z with (Z.ones 4) in H. rewrite Z.land_ones in H by lia. exact H.
Qed.

(* [comment removed for export] *)
Definition cbyte_ : ltac2:(zQ "20!j7!lb>1c@1$1@1$0#k0@1$1@1$0#8") := ltac2:(zQ "40!j7!ir0!lb!hu7\1c@1$2@1$0#k0@2$1@1$0#8@2$3@1$0#k0^1").
Definition cpat_ : ltac2:(zQ "20!j7!lb>1c@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "60!j7!ive!jg4!ir0!lb!hu7\1c@1$4@1$0#k0@2$3@1$0#k0@2$2@2$5@1$0#k0^1$1").

Lemma cpat_bytes : ltac2:(zQ "a0!j7!lb!h8!il6!ji2!jm3!jn8!jo2!ig2!hu7>1c@1$1@1$0#k0>0@2$8@2$9@1$0#k0^1+hg0@3$3@1$2@1$1@1$0#8@2$5N8@1$7^2@3$4@1$1@1$0#8@1$6^2N8").
Proof. intros c Hc. pose proof (u64_range c). apply rep8_bytes. lia. Qed.
End FPX1.

Section IMEMSET.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable segs : ltac2:(zQ "20!h8!mo2@1$0$1").
  Variable base : word.
  Variable mem0 : ltac2:(zQ "30!j7!lb!mhb>0@1$1@1$0#k0@1$2@1$1@1$0#8").
  Variables s c : word.
  Variable n : Z.
  Variable rom : ltac2:(zQ "30!j7!lb!mhb>0@1$1@1$0#k0@1$2@1$1@1$0#8").
  Hypothesis HCODE : ltac2:(zQ "20!lr2!ls3@4$1?4segs?4baseZ$0").
  Hypothesis Hn : ltac2:(zQ "10!hv5@2$0Z?1n").
  Hypothesis Hnw : ltac2:(zQ "50!j7!lg3!ig2!iq9!hu7@2$2@2$1@2$4@1$0#k0?1s?1n@2$3+2+k0").
  Hypothesis Hok : ltac2:(zQ "50!mi3!mi9!il6!mj6!lke@3$2$0@4$3?4segs?4mem0?1s@1$4?1n$1").
  (* [comment removed for export] *)
  Hypothesis HC256 : ltac2:(zQ "70!il6!hrc!mif!j7!mk2!ig2!hu7>0@3$0$1@2$4?1n?1sZ>0@1$2@3$0$1?1nZ@2$5@2$6@1$3#k0?1c+hg0").

  #[local] Abbreviation cbyte := (cbyte_ c).
  #[local] Abbreviation cpat := (cpat_ c).
  #[local] Abbreviation MS := (msetk mem0 s (cbyte_ c)).
  #[local] Abbreviation CL := (fun r => In r imemset_clob).

  (* [comment removed for export] *)
  Ltac get_code :=
    let HC := fresh "HC" in
    pose proof HCODE as HC; cbn [code_at imemset_words Z.add Pos.add Pos.succ] in HC;
    destruct HC as (C0 & C4 & C8 & C12 & C16 & C20 & C24 & C28 & C32 & C36 & C40 & C44 & C48 & C52 & C56 & C60 & C64 & C68 & C72 & C76 & C80 & C84 & C88 & C92 & _).

  (* [comment removed for export] *)
  Ltac msb F D kk :=
    chain_step; [reflexivity
      | eapply MmapSim.step_sb_at with (a := at_ s kk) (v := c) (b := cbyte);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity | reflexivity
        | apply (wr_s segs mem0 s n cbyte Hn Hnw Hok); cbn; lia ]
      | step_simpl];
    rewrite (msetk_extend1 mem0 s cbyte kk) by lia; vn.

  (* [comment removed for export] *)
  Ltac msd F D kk :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := at_ s kk) (v := cpat);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | apply (wr_s segs mem0 s n cbyte Hn Hnw Hok); cbn; lia ]
      | step_simpl];
    rewrite (cpat_bytes c) by lia;
    rewrite (msetk_extend mem0 s cbyte kk 8) by lia; change (Z.of_nat 8) with 8%Z; zlit_at; vn.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma bl_loop : ltac2:(zQ "h90!j7!lb!il6!hqb!job!hr0!hr5!jr9!jva!hvb!hrc!kjf!kk9!kl1!kla!km1!km6!kmc!kr5!krf!ksd!kua!hv5!ig2!kv0>1i$f>4regs@2$7@1$0#5@1$1@1$0#k0>3ret@1$1@1$0#k0>1k$a>0@1$h4^2>0@3$2@1$1@1$0#k0@2$4^4@3$5@1$0#5+1Kv$3@2$6@1$0#5+1^3>0@3$2@1$1@1$0#k0@2$4^5@3$5@1$0#5+bKv$3@2$6@1$0#5+b?1c>0@3$2@1$1@1$0#k0@2$4^6@3$5@1$0#5+dKv$3@2$6@1$0#5+d@2$8?1s^4>0@3$2@1$1@1$0#k0@2$4^7@3$5@1$0#5+cKv$3@2$6@1$0#5+c@2$8?1s?1n>0@2$9@2$h6Z^6@2$h7^6?1n>0@3$2$a@1$h8^a@2$e@2$e?1n+1^7@2$h0@2$7@1$0#5@1$1@1$0#k0\5regs'@2$7@1$0#5@1$1@1$0#k0@2$9@3$h2?4segs@5$c?2fx^b@2$8?4base+h8@4$d?4mem0?1s@1$b?1c^9?3rom@5$c?2fx^1^a@4$d?4mem0?1s@1$b?1c?1n?3rom@3$h3\1r@1$1@1$0#5@3$h5@1$1@1$0#5^1$h1^b^1").
  Proof.
    get_code. pose proof (u64_range s) as Hs.
    induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 Hk Hi.
    - eexists. split.
      + msb C24 D_a2290 k.                        (* [comment removed for export] *)
        an C28 D_a2294.                           (* [comment removed for export] *)
        ab_ft C32 D_a2298 ltac:(condz).           (* [comment removed for export] *)
        an C36 D_a229c.                           (* [comment removed for export] *)
        aret C92 D_a22d4 ret.
        replace (k + 1)%Z with n by lia. apply mst_refl.
      + unfold imemset_clob. solve_regs_agree.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 24) (MS (k + 1)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = c /\ getr r 13 = at_ s (k + 1)
                         /\ getr r 12 = at_ s n /\ regs_agree CL regs r)).
      + eexists. split.
        * msb C24 D_a2290 k.
          an C28 D_a2294.
          ab_tk C32 D_a2298 ltac:(condz).         (* [comment removed for export] *)
          apply mst_refl.
        * post. unfold imemset_clob. solve_regs_agree.
      + cbv beta. (intros r1 nd_i1; ndestruct nd_i1 as (R1 & R11 & R13 & R12 & AG)).
        ndestruct (IH r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2).
        exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma al_loop : ltac2:(zQ "hd0!j7!lb!il6!hqb!job!hr0!hr5!jr9!jva!hrc!kjf!kk9!kl1!hv5!kla!km1!hvb!km6!kva!kmc!kr5!krf!ksd!kua!lg3!ig2!jg4!kv0!hu7>1i$f>4regs@2$7@1$0#5@1$1@1$0#k0>3ret@1$1@1$0#k0>1k$9>0@1$h6^2>0@3$2@1$1@1$0#k0@2$4^4@3$5@1$0#5+1Kv$3@2$6@1$0#5+1^3>0@3$2@1$1@1$0#k0@2$4^5@3$5@1$0#5+bKv$3@2$6@1$0#5+b@1$h2?1c>0@3$2@1$1@1$0#k0@2$4^6@3$5@1$0#5+dKv$3@2$6@1$0#5+d@2$8?1s^4>0@3$2@1$1@1$0#k0@2$4^7@3$5@1$0#5+cKv$3@2$6@1$0#5+c@2$8?1s?1n>0@2$dZ^6>0@2$d@2$h8^7+h0?1n>0@3$2$9@2$ha@1$hb^b+h0@2$e@2$e?1n^8+h0>0@2$h9@2$hc@1$0#k0?1c+hg0@2$h1@2$7@1$0#5@1$1@1$0#k0\5regs'@2$7@1$0#5@1$1@1$0#k0@2$h0@3$h4?4segs@5$b?2fx^d@2$8?4base+kc@4$c?4mem0?1s@1$a?1c^b?3rom@5$b?2fx^1^c@4$c?4mem0?1s@1$a?1c?1n?3rom@3$h5\1r@1$1@1$0#5@3$h7@1$1@1$0#5^1$h3^d^1").
  Proof.
    get_code. pose proof (u64_range s) as Hs. pose proof (u64_range c) as Hc.
    induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 Hk Hk16 Hi Hc256.
    - eexists. split.
      + msd C76 D_a22c4 k.                        (* [comment removed for export] *)
        msd C80 D_a22c8 (k + 8)%Z.                (* [comment removed for export] *)
        an C84 D_a22cc.                           (* [comment removed for export] *)
        ab_ft C88 D_a22d0 ltac:(condz).           (* [comment removed for export] *)
        aret C92 D_a22d4 ret.
        replace (k + 8 + 8)%Z with n by lia. apply mst_refl.
      + unfold imemset_clob. solve_regs_agree.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 76) (MS (k + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = cpat /\ getr r 13 = at_ s (k + 16)
                         /\ getr r 12 = at_ s n /\ regs_agree CL regs r)).
      + eexists. split.
        * msd C76 D_a22c4 k.
          msd C80 D_a22c8 (k + 8)%Z.
          an C84 D_a22cc.
          ab_tk C88 D_a22d0 ltac:(condz).         (* [comment removed for export] *)
          replace (k + 8 + 8)%Z with (k + 16)%Z by lia. apply mst_refl.
        * post. unfold imemset_clob. solve_regs_agree.
      + cbv beta. (intros r1 nd_i2; ndestruct nd_i2 as (R1 & R11 & R13 & R12 & AG)).
        ndestruct (IH r1 ret (k + 16)%Z Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia) ltac:(lia) Hc256) as (r2 & RUN & AG2).
        exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem imemset_run : ltac2:(zQ "h60!j7!lb!hqb!il6!job!hr0!hr5!jr9!kk9!hvb!km6!ji2!kjf!kmc!lk4!kr5!jva!krf!ksd!kua!lke!ir0>4regs@2$7@1$0#5@1$1@1$0#k0>3ret@1$1@1$0#k0>0@1$h2^1>0@3$3@1$1@1$0#k0@2$4^3@3$5@1$0#5+1Kv$2@2$6@1$0#5+1^2>0@3$3@1$1@1$0#k0@2$4^4@3$5@1$0#5+aKv$2@2$6@1$0#5+a?1s>0@3$3@1$1@1$0#k0@2$4^5@3$5@1$0#5+bKv$2@2$6@1$0#5+b?1c>0@3$3@1$1@1$0#k0@2$4^6@3$5@1$0#5+cKv$2@2$6@1$0#5+c@2$h5@1$0#k0?1n@2$a@2$7@1$0#5@1$1@1$0#k0\5regs'@2$7@1$0#5@1$1@1$0#k0@2$9@3$f?4segs@5$8?2fx^8@2$h0?4baseZ?4mem0?3rom@5$8?2fx^1^7@3$e?4mem0?1s@3$b@1$1@1$0#8@1$c?1c@1$h4?1n?3rom@3$h1\1r@1$1@1$0#5@3$h3@1$1@1$0#5^1$d^8^1").
  Proof.
    get_code. intros regs ret Hret H1 H10 H11 H12.
    pose proof (u64_range s) as Hs. pose proof (u64_range c) as Hc.
    pose proof (align15_range n s Hn) as HA.
    change (wbytes mem0 s (repeat (cbyte_ c) (Z.to_nat n))) with (MS n). change mem0 with (MS 0).
    (* [comment removed for export] *)
    eapply (runs_trans segs _ (fun r => mkst r (at_ base 8) (MS 0) rom)
             (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 11 = c /\ getr r 12 = Z_to_bv 64 n
                       /\ getr r 13 = Z_to_bv 64 (align15 n s) /\ regs_agree CL regs r)).
    { eexists. split.
      - an C0 D_a2278.                            (* [comment removed for export] *)
        av C4 D_a227c (Z_to_bv 64 (align15 n s))
           ltac:(rewrite <- (u_align15 n s) by lia; symmetry; apply Z_to_bv_bv_unsigned).  (* [comment removed for export] *)
        apply mst_refl.
      - post. unfold imemset_clob. solve_regs_agree. }
    cbv beta. (intros r0 nd_i3; ndestruct nd_i3 as (R1 & R10 & R11 & R12 & R13 & AG0)).
    destruct (Z.eq_dec (align15 n s) 0) as [HA0|HA0].
    - (* [comment removed for export] *)
      destruct (Z.eq_dec n 0) as [Hz|Hnz].
      + eexists. split.
        * ab_tk C8 D_a2280 ltac:(condz).          (* [comment removed for export] *)
          ab_tk C40 D_a22a0 ltac:(condz).         (* [comment removed for export] *)
          aret C92 D_a22d4 ret.
          rewrite Hz. apply mst_refl.
        * exact AG0.
      + pose proof (HC256 HA0 Hnz) as Hc256.
        pose proof (align15_n16 n s Hn HA0) as Hn16.
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 76) (MS 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = cpat /\ getr r 13 = at_ s 0
                           /\ getr r 12 = at_ s n /\ regs_agree CL regs r)).
        * eexists. split.
          -- ab_tk C8 D_a2280 ltac:(condz).       (* [comment removed for export] *)
             ab_ft C40 D_a22a0 ltac:(condz).      (* [comment removed for export] *)
             av C44 D_a22a4 (at_ s n) ltac:(apply v_add_at; lia).           (* [comment removed for export] *)
             av C48 D_a22a8 (Z_to_bv 64 (bv_unsigned c * 2 ^ 8)) ltac:(apply v_slli_mul; lia).  (* [comment removed for export] *)
             av_or C52 D_a22ac (Z_to_bv 64 (bv_unsigned c * 257))
               ltac:(rewrite v_or_shl by (unorm; lia); f_equal; lia).                        (* [comment removed for export] *)
             av C56 D_a22b0 (Z_to_bv 64 (bv_unsigned c * 257 * 2 ^ 16))
               ltac:(rewrite v_slli_mul by lia; unorm; reflexivity).                          (* [comment removed for export] *)
             av_or C60 D_a22b4 (Z_to_bv 64 (bv_unsigned c * 16843009))
               ltac:(rewrite v_or_shl by (unorm; lia); unorm; f_equal; lia).                 (* [comment removed for export] *)
             av C64 D_a22b8 (Z_to_bv 64 (bv_unsigned c * 16843009 * 2 ^ 32))
               ltac:(rewrite v_slli_mul by lia; unorm; reflexivity).                          (* [comment removed for export] *)
             av_or C68 D_a22bc (cpat_ c)
               ltac:(rewrite v_or_shl by (unorm; lia); unfold cpat_, M8; unorm; f_equal; lia). (* [comment removed for export] *)
             an C72 D_a22c0.                      (* [comment removed for export] *)
             apply mst_refl.
          -- post; rewrite ?at_0; try reflexivity. unfold imemset_clob. ra_chain.
        * cbv beta. (intros r1 nd_i4; ndestruct nd_i4 as (S1 & S11 & S13 & S12 & AG1)).
          assert (Hdiv : (n = 16 * (n / 16))%Z) by (pose proof (Z.div_mod n 16 ltac:(lia)); lia).
          assert (Hi : exists i : nat, (Z.of_nat i * 16 = n - 0 - 16)%Z) by (exists (Z.to_nat (n / 16 - 1)); lia).
          destruct Hi as (i & Hi).
          ndestruct (al_loop i r1 ret 0 Hret S1 S11 S13 S12 ltac:(lia) ltac:(lia) Hi Hc256) as (r2 & RUN & AG2).
          exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
    - (* [comment removed for export] *)
      destruct (Z.eq_dec n 0) as [Hz|Hnz].
      + eexists. split.
        * ab_ft C8 D_a2280 ltac:(condz).          (* [comment removed for export] *)
          ab_tk C12 D_a2284 ltac:(condz).         (* [comment removed for export] *)
          aret C92 D_a22d4 ret.
          rewrite Hz. apply mst_refl.
        * exact AG0.
      + eapply (runs_trans segs _ (fun r => mkst r (at_ base 24) (MS 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = c /\ getr r 13 = at_ s 0
                           /\ getr r 12 = at_ s n /\ regs_agree CL regs r)).
        * eexists. split.
          -- ab_ft C8 D_a2280 ltac:(condz).       (* [comment removed for export] *)
             ab_ft C12 D_a2284 ltac:(condz).      (* [comment removed for export] *)
             av C16 D_a2288 (at_ s n) ltac:(apply v_add_at; lia).           (* [comment removed for export] *)
             an C20 D_a228c.                      (* [comment removed for export] *)
             apply mst_refl.
          -- post; rewrite ?at_0; try reflexivity. unfold imemset_clob. ra_chain.
        * cbv beta. (intros r1 nd_i5; ndestruct nd_i5 as (S1 & S11 & S13 & S12 & AG1)).
          ndestruct (bl_loop (Z.to_nat (n - 1)) r1 ret 0 Hret S1 S11 S13 S12 ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2).
          exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
  Qed.
End IMEMSET.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.

(* [comment removed for export] *)
Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition asan_imemset_entry : word := 0x0a2218.

Lemma asan_imemset_code : ltac2:(zQ "40!lpb!lr2!ls3!mg8@4$2$3$0Z$1").
Proof. unfold imemset_words. code_at_vm. Qed.

Theorem asan_imemset : ltac2:(zQ "i21!j7!lb!il6!hqb!job!hr0!hr5!hrc!jr9!hu7!mhb!kk9!mg8!ig2!lke!ir0!mi3!mi9!hvb!km6!mif!ji2!mj6!lpb!mk2!kmc!lk4!kr5!krf!ksd!kua!lg3!hv5!iq9&>0@1$1@1$0#k0@1$a@1$1@1$0#8>4mem0~0>1s@1$1@1$0#k0>1c@1$1@1$0#k0>1n$7>3rom~0>4regs@2$8@1$0#5@1$1@1$0#k0>3ret@1$1@1$0#k0>0@2$i0Z^4>0@2$d@2$hf@2$9@1$0#k0^7^5@2$i1+2+k0>0@3$2$h0@4$h6$c^9^8@1$e^6$h1>0>0@3$2$7@2$h8^7^9Z>0@1$h4@3$2$7^8Z@2$d@2$9@1$0#k0^a+hg0>0@1$hd^5>0@3$2@1$1@1$0#k0@2$4^7@3$5@1$0#5+1Kv$3@2$6@1$0#5+1^6>0@3$2@1$1@1$0#k0@2$4^8@3$5@1$0#5+aKv$3@2$6@1$0#5+a^c>0@3$2@1$1@1$0#k0@2$4^9@3$5@1$0#5+bKv$3@2$6@1$0#5+b^c>0@3$2@1$1@1$0#k0@2$4^a@3$5@1$0#5+cKv$3@2$6@1$0#5+c@2$f@1$0#k0^c@2$h3@2$8@1$0#5@1$1@1$0#k0\5regs'@2$8@1$0#5@1$1@1$0#k0@2$h2@3$hb$c@5$b?2fx^c$h7^h1^d@5$b?2fx^1^b@3$ha^h1^h0@3$h5@1$1@1$0#8@2$f@1$0#8@2$9@1$0#k0^f@1$e^e^d@3$hc\1r@1$1@1$0#5@3$he@1$1@1$0#5^1$h9^c^1").
Proof.
  intros mem0 s c n rom regs ret Hn Hnw Hok HC256.
  rewrite <- (at_0 asan_imemset_entry).
  apply (imemset_run _ _ mem0 s c n rom asan_imemset_code Hn Hnw Hok HC256).
Qed.
End FPX2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
