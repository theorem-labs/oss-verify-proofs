(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import StreamSim.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init5Logichc2eq04Npos46Stdlib6ZArith6BinInt1Zjb6modulojb3pow35stdpp9bitvectorbdefinitionsm27bv_wrap01N37Corelib7StringsaPrimStringoc6string57Corelib7Numbers6Cyclic5Int63cUint63Axiomsr14to_Zoc6lengthjb3divjb4to_N37Corelib4Init9Datatypesv94boolv96option3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshi1fsegment_byte_at79OSSVerify6Proofsaboost_jsonafuzz_parse3lib7SegRead7SEGREAD~~~~~~hmbbchunk_bytesm22bvv94consv94listhi1bhex_byte_at46Stdlib6NArith6BinNat1Nhte3ltbhte3subv93natv94Nonev94truehc3not37Corelib4Init5Peanoihe2lthmb8bytes_okhte3addhte6of_nat3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeil57Segmentjb4of_Nil58seg_basejb3addjb2lev94Somehc3andil58seg_sizehmbh3find_segment_stricthi1cfind_segmentv94andbv95falseil59seg_bytesil5cseg_writablejb6of_natjb3subhc2exhmberange_writablejb2ltm2bbv_unsignedhc1Im22BVm24BvWfm26bv_add69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9StreamSim~~~~~~jn27wseg_ok" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module SEGREAD.
Lemma bv_wrap64_mod : ltac2:(zQ "60!h9!j0!j5!l3!lc!nf>1z$0@3$1$0@2$5@1$2#k0^1@2$3^1@2$4+2+k0").
Proof. reflexivity. Qed.

Definition chunk_bytes : ltac2:(zQ "20!o9!q8>1c$1$0") := ltac2:(zQ "50!tc!u3!q8!uc!v2\1c$2@1$4@2$3@1$0@1$1^1+2").

(* [comment removed for export] *)
Fixpoint bytes_ok (chunks : list PrimString.string) (off : N) (n : nat) {struct chunks} : bool :=
  match chunks with
  | [] => match n with O => true | S _ => false end
  | c :: rest =>
      let cb := chunk_bytes c in
      (fix go (off : N) (n : nat) {struct n} : bool :=
         match n with
         | O => true
         | S n' => if (off <? cb)%N then match hex_byte_at c off with Some _ => go (off + 1)%N n' | None => false end
                   else bytes_ok rest (off - cb)%N n
         end) off n
  end.

Lemma segment_byte_at_cons : ltac2:(zQ "e0!q8!hh1!hh8!j5!hl8!hqd!hrc!hs1!hs8!j0!o9!hsf!hv6!hvd>1c$0>4rest@1$8$0>3off$a@3$9@1$2@1$6@1$3#8@2$4@3$7$0^3^2^1M1\0$1@1$2@1$6@1$3#8@2$c^1@1$5^3@2$b^3^1@2$4^2@2$d^1@1$5^3").
Proof. reflexivity. Qed.

Lemma bytes_ok_sound : ltac2:(zQ "h10!ig4!j0!j5!hrc!iga!hh1!hs8!hh8!ih1!ih8!ij2!o9!q8!hl8!ij8!ik4!ikb>6chunks@1$6$c>3off$b>1n$0>0@3$1$5@3$e^3^2^1$8>1i$0>0@2$a^1^3@1$9@3$1@1$7@1$3@1$2#8@2$d^6@2$f^5@1$h0^2@1$4@1$3@1$2#8").
Proof.
  induction chunks as [|c rest IH]; intros off n H i Hi.
  - cbn in H. destruct n; [lia | discriminate].
  - revert off H i Hi. induction n as [|n' IHn]; intros off H i Hi; [lia|].
    cbn [bytes_ok] in H. fold (bytes_ok rest) in H.
    rewrite segment_byte_at_cons.
    destruct (N.ltb_spec off (chunk_bytes c)) as [Hlt|Hge].
    + destruct (hex_byte_at c off) as [b|] eqn:Hb; [|discriminate].
      destruct i as [|i'].
      * rewrite N.add_0_r. destruct (N.ltb_spec off (chunk_bytes c)); [|lia]. rewrite Hb. discriminate.
      * specialize (IHn (off + 1)%N H i' ltac:(lia)).
        replace (off + N.of_nat (S i'))%N with (off + 1 + N.of_nat i')%N by lia.
        rewrite segment_byte_at_cons in IHn. exact IHn.
    + (* [comment removed for export] *)
      pose proof (IH (off - chunk_bytes c)%N (S n') H i Hi) as X.
      destruct (N.ltb_spec (off + N.of_nat i) (chunk_bytes c)); [lia|].
      replace (off + N.of_nat i - chunk_bytes c)%N with (off - chunk_bytes c + N.of_nat i)%N by lia. exact X.
Qed.

(* [comment removed for export] *)
Fixpoint find_segment_strict (segs : list Segment) (lo n : Z) : option Segment :=
  match segs with
  | [] => None
  | seg :: rest =>
      let base := Z.of_N (seg_base seg) in
      let top := base + Z.of_N (seg_size seg) in
      if (Z.leb base lo && Z.leb (lo + n) top)%bool then Some seg
      else if (Z.leb top lo || Z.leb (lo + n) base)%bool then find_segment_strict rest lo n else None
  end.

Lemma find_segment_strict_base : ltac2:(zQ "d0!ioa!ip5!h9!ipc!iq8!iqe!ir3!hs8!hh8!ira!j0!is0!isc>4segs@1$7$0>2lo$2>1n$2>3seg$0>0@3$a@1$8$0@3$c^4^3^2@2$6$0^1@2$9@2$5@1$1@1$3^2^4@2$5@2$4^4^3@2$4@1$1@1$3^2@1$1@1$b^2").
Proof.
  induction segs as [|s rest IH]; intros lo n seg H; [discriminate|]. cbn [find_segment_strict] in H.
  destruct (Z.leb_spec (Z.of_N (seg_base s)) lo); destruct (Z.leb_spec (lo + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s))); cbn [andb] in H.
  - injection H as <-. lia.
  - destruct (_ || _)%bool; [apply IH; exact H | discriminate].
  - destruct (_ || _)%bool; [apply IH; exact H | discriminate].
  - destruct (_ || _)%bool; [apply IH; exact H | discriminate].
Qed.

Lemma find_segment_strict_sound : ltac2:(zQ "a0!ioa!h9!ir3!hh8!j0!iq8!iqe!hs8!iu4!isc>4segs@1$7$0>2lo$1>1n$1>3seg$0>1a$1>0@3$4@1$3$0@3$9^5^4^3@2$2$0^2>0@2$6^5^2>0@2$6@2$5^3+1@2$5^6^5@3$4@1$3$0@3$8^8^4+1@2$2$0^5").
Proof.
  induction segs as [|s rest IH]; intros lo n seg a H Ha1 Ha2; [discriminate|].
  cbn [find_segment_strict] in H. cbn [find_segment].
  destruct (Z.leb_spec (Z.of_N (seg_base s)) lo) as [B1|B1];
    destruct (Z.leb_spec (lo + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s))) as [B2|B2]; cbn [andb] in H.
  - injection H as <-.
    destruct (Z.leb_spec (Z.of_N (seg_base s)) a); [|lia]. destruct (Z.leb_spec (a + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s))); [reflexivity|lia].
  - destruct (Z.leb_spec (Z.of_N (seg_base s) + Z.of_N (seg_size s)) lo) as [C|C]; cbn [orb] in H.
    + destruct (Z.leb_spec (Z.of_N (seg_base s)) a); destruct (Z.leb_spec (a + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s))); cbn [andb]; try (exfalso; lia); eapply IH; eauto.
    + destruct (Z.leb_spec (lo + n) (Z.of_N (seg_base s))) as [D|D]; [|discriminate].
      destruct (Z.leb_spec (Z.of_N (seg_base s)) a); destruct (Z.leb_spec (a + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s))); cbn [andb]; try (exfalso; lia); eapply IH; eauto.
  - destruct (Z.leb_spec (Z.of_N (seg_base s) + Z.of_N (seg_size s)) lo) as [C|C]; cbn [orb] in H.
    + destruct (Z.leb_spec (Z.of_N (seg_base s)) a); destruct (Z.leb_spec (a + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s))); cbn [andb]; try (exfalso; lia); eapply IH; eauto.
    + destruct (Z.leb_spec (lo + n) (Z.of_N (seg_base s))) as [D|D]; [|discriminate].
      destruct (Z.leb_spec (Z.of_N (seg_base s)) a); destruct (Z.leb_spec (a + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s))); cbn [andb]; try (exfalso; lia); eapply IH; eauto.
  - destruct (Z.leb_spec (Z.of_N (seg_base s) + Z.of_N (seg_size s)) lo) as [C|C]; cbn [orb] in H.
    + destruct (Z.leb_spec (Z.of_N (seg_base s)) a); destruct (Z.leb_spec (a + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s))); cbn [andb]; try (exfalso; lia); eapply IH; eauto.
    + destruct (Z.leb_spec (lo + n) (Z.of_N (seg_base s))) as [D|D]; [|discriminate].
      destruct (Z.leb_spec (Z.of_N (seg_base s)) a); destruct (Z.leb_spec (a + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s))); cbn [andb]; try (exfalso; lia); eapply IH; eauto.
Qed.

Definition range_writable : ltac2:(zQ "50!hh1!hs8!ig4!h9!ioa>4segs@1$1$4>2lo$3>1n$2$0") := ltac2:(zQ "h10!ioa!hh8!iv4!hh1!ivb!hs8!ig4!h9!ipc!jg3!jh0!ij8!isc!ip5!ji0!ji9!v2\4segs@1$5$0\2lo$7\1n$6M1\1x@1$1$0$3@3$c^3^2@1$e^1\3seg$0@2$2@1$a^1@3$b@1$9^1@1$h0@2$f^3@1$d@1$8^1^2$4").


(* [comment removed for export] *)
Lemma range_writable_point : ltac2:(zQ "hc0!ioa!j0!ira!hh1!hh8!ih1!j5!h9!hrc!iga!ir3!hs8!ig4!jif!ih8!ipc!jg3!jh0!iu4!hl8!jj4!iq8!iqe!jk6!ip5!ji0!ji9!v2>4segs@1$b$0>2lo$7>1n$c>1u$7>0@3$1$3@3$h4^4^3^2$5>0@2$2@2$h6^4^2@2$h7^2@2$h5^4@1$h9^3@2$d$0\3seg$0@2$2@3$1@1$4$0@3$h2^7^4+1@2$a$0^1@2$2@3$1$3@1$h1^1$5@1$e@3$1@1$4@1$8@1$6#8@2$h3@1$h0^1@1$hb@2$ha^4@1$h8@1$f^1@1$9@1$8@1$6#8").
Proof.
  intros segs lo n u H Hu. unfold range_writable in H.
  destruct (find_segment_strict segs lo (Z.of_nat n)) as [seg|] eqn:Hf; [|discriminate].
  apply andb_prop in H as [Hw Hb]. pose proof (find_segment_strict_base _ _ _ _ Hf) as [B1 B2].
  exists seg. split; [apply (find_segment_strict_sound segs lo (Z.of_nat n) seg u Hf); lia|]. split; [exact Hw|].
  replace (Z.to_N (u - Z.of_N (seg_base seg))) with (Z.to_N (lo - Z.of_N (seg_base seg)) + N.of_nat (Z.to_nat (u - lo)))%N by lia.
  apply (bytes_ok_sound _ _ _ Hb). lia.
Qed.

Lemma bv_unsigned_add1 : ltac2:(zQ "c0!j5!jkb!iq8!jl9!j0!h9!jk6!lc!jld!jm2!hrc!jm9>1a@1$a@1$0#k0>0@2$6@2$2@2$1@1$0#k0^1+1@2$7+2+k0@3$4$5@2$1@1$0#k0@3$b@1$0#k0^2@3$8@1$0#k0+1Kv$3@2$9@1$0#k0+1@2$2@2$1@1$0#k0^2+1").
Proof.
  intros a Ha. rewrite bv_add_unsigned. change (bv_unsigned (1 : word)) with 1%Z. rewrite bv_wrap64_mod.
  apply Z.mod_small. pose proof (bv_unsigned_in_range _ a). lia.
Qed.

(* [comment removed for export] *)
Theorem wseg_ok_range : ltac2:(zQ "f0!j5!hh1!ih1!j0!jkb!hs8!ig4!ioa!jj4!jqe!iq8!iqe!ji0!lc!hrc>4segs@1$5$7>1a@1$e@1$0#k0>1n$6>0@3$3$1@3$8^3@2$4@1$0#k0^2^1$2>0@2$b@2$a@2$4@1$0#k0^3@1$c^2@2$d+2+k0@3$3$1@3$9^5^4^3$2").
Proof.
  intros segs a n H Hn.
  assert (P : forall u, bv_unsigned a <= u < bv_unsigned a + Z.of_nat n ->
            exists seg, find_segment segs u 1 = Some seg /\ seg_writable seg = true
                        /\ segment_byte_at (seg_bytes seg) (Z.to_N (u - Z.of_N (seg_base seg))) <> None)
    by (intros u Hu; exact (range_writable_point segs _ n u H Hu)).
  clear H. revert a Hn P. induction n as [|n' IH]; intros a Hn P; [reflexivity|].
  rewrite Nat2Z.inj_succ in Hn, P. pose proof (bv_unsigned_in_range _ a) as Ha.
  cbn [wseg_ok]. destruct (P (bv_unsigned a) ltac:(lia)) as [seg [Hs [Hw Hb]]].
  rewrite Hs, Hw. destruct (segment_byte_at (seg_bytes seg) (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)))) as [b|]; [|exfalso; apply Hb; reflexivity].
  cbn [andb]. destruct n' as [|n'']; [reflexivity|]. rewrite Nat2Z.inj_succ in Hn, P.
  apply IH; rewrite Nat2Z.inj_succ.
  - rewrite bv_unsigned_add1 by lia. lia.
  - intros u Hu. rewrite bv_unsigned_add1 in Hu by lia. apply P. lia.
Qed.
End SEGREAD.
(* [comment removed for export] *)
