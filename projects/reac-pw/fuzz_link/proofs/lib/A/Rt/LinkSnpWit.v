(* reac-pw/fuzz_link, image A (the asan build, pin 059dae63e07c): satisfiability witnesses of `asnprintf_link_fpre` (LinkSnpDef.v),
   the function-specific premises of the ONE snprintf contract at link's wrapper LA_W_SNPRINTF 0x43088, at FF = FF_link
   and K = LINK_SNP_STK, one lemma per call site (link-a/libc/printf.md (internal record, sha256 7bbba2c3aa7f) section 1):
   - snw_s2_apre_sat: S2, LLVMFuzzerTestOneInput 0x82b14, snprintf(g_names + 8i, 8, "nl%d", i) at i = 0:
     d = g_names 0x62fac0 (.bss: the destination takes link_snp_place's second arm), n = 8, f = .str 0x20fa0 "nl%d",
     a3 = 0; T = "nl0", w = sn_len 7 T = 4;
   - snw_s1_apre_sat: S1, remember 0x89ea8 (tail `j`), snprintf(blk + 4 + 16k, 16, "%s", name) at k = 0:
     d = 0x602000000014 (mark's block, calloc(1, 0x204), at 0x602000000010, + 4), n = 16, f = .str.37 0x21680 "%s",
     a3 = the name "eth0" at 0x603000000040; T = "eth0", w = sn_len 15 T = 5;
   - snw_s3_apre_sat: S3, LLVMFuzzerTestOneInput 0x839c4, snprintf(blk + 0x2094 + 16k, 16, "%s", name) at k = 0:
     d = 0x625000002194 (blk, calloc(1, 0x2298), at 0x625000000100, + 0x2094), n = 16, f = .str.21 0x21240 "%s",
     the same name; T = "eth0", w = 5.
   S1 and S3 are one lemma, snw_pct_apre_sat, over the two (f, d) pairs.
   Each lemma: for EVERY segment list segs and every register file with a0 = d, a1 = n, a2 = f, a3 as above and
   sp = SNW_SP 0x7ffffffde000 (form_witness.v's CA_SP), the bundle holds at the world snw_W segs (hidden-byte map
   constantly false, no allocation intervals: H_off_segments holds because the map is false, A_wf [] by Forall_nil),
   at xs = [] (the argument words are a3..a7, va_words) and at cval = SNW_CVAL. The memory (snw_mem2 for S2,
   snw_memh for S1 and S3) holds every byte the premises read, so no ROM byte is read and no lemma depends on segs.
   The memories, and why each byte is what a real call has there:
   - image A's own bytes: the stack-guard .got word 0xa2658 holds LA_GUARD 0x651c50 (AF0m.v Tfib_const_abs); the
     format literals "nl%d\0" at 0x20fa0, "%s\0" at 0x21680 and at 0x21240 (.rodata; their ASan global descriptors
     in AF0m.v give the sizes 5, 3, 3); the shadow word of each literal's granule as AF0m.v gives it:
     0x7fffc1f0..f7 = 0 0 0 0 5 f9 f9 f9, 0x7fffc2d0..d7 = 3 f9 f9 f9 0 0 0 0, 0x7fffc248..4f = 3 f9 f9 f9 2 f9 f9 f9
     (Tfib_const_shadow's rows; the zeros are the shadow of Tfib_zero_shadow's ranges (IMG_LO, 0x20fa0 - IMG_LO)
     and (0x216a0, ...)); g_names' 512 bytes (descriptor size 0x200; .bss, zero before the loop first writes it)
     and their shadow 0x800bdf58..0x800bdf97 (zero: Tfib_zero_shadow's (0x62fac0, 0x200));
   - run state, as a run has it: __stack_chk_guard at 0x651c50 holds SNW_CVAL (the start-up copies it from
     AT_RANDOM and musl zeroes its second byte; the premises leave cval free, so the value is chosen); the two
     calloc blocks (zero bytes; the shadow bytes of the granules the destination covers are 0, as ASan holds them
     for granules inside a live block); a 16-byte heap buffer for the name, "eth0", its NUL, then zeros, with the
     shadow byte of its granule 0 (link's real names are g_names slots or strings of the `odd` table; a heap string
     is chosen here only to show the premises satisfiable, and the family admits either);
   - left free by the premises and chosen 0: the other bytes of the shadow words of the two destinations and of
     the name (shadow_hull_vis asks only that they are present; in a run the destination word of S1 starts with
     the shadow of the chunk header, the name's word goes on into its redzone), and the name buffer's bytes after
     its NUL (pf_arg_asan asks the rest of the granule, up to str_end, to be present).
   The heap addresses are chosen: the premises ask only that d lie above IMG_TOP 0x654000, in ASan's high memory
   (amem_range), apart from the format, the name and the window. The two blocks, the name buffer and the stack
   window [sp - 8192, sp) are pairwise apart.
   Proves no function (kind: statement text: satisfiability witnesses). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import PfFacts SnShared.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkSnpDef.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Range checks by computation
   ========================================================================== *)

(* a in [lo, lo + n) *)
Definition inrz (a lo n : Z) : bool := (lo <=? a) && (a <? lo + n).

Definition is_someb {A : Type} (o : option A) : bool := match o with Some _ => true | None => false end.

(* every x in [lo, lo + n) satisfies p *)
Definition zall (lo n : Z) (p : Z -> bool) : bool :=
  List.forallb (fun k => p (lo + Z.of_nat k)) (List.seq 0 (Z.to_nat n)).

Lemma zall_spec : forall lo n p, zall lo n p = true -> forall x, lo <= x < lo + n -> p x = true.
Proof.
  intros lo n p H x Hx. unfold zall in H. pose proof (proj1 (forallb_forall _ _) H) as H'. cbv beta in H'.
  assert (E : lo + Z.of_nat (Z.to_nat (x - lo)) = x) by (rewrite Z2Nat.id by lia; lia).
  rewrite <- E. apply H'. apply (proj2 (in_seq _ _ _)). lia.
Qed.

Lemma snw_some : forall (rd : reader) lo n, zall lo n (fun x => is_someb (rd x)) = true ->
  forall x, lo <= x < lo + n -> rd x <> None.
Proof.
  intros rd lo n H x Hx. pose proof (zall_spec lo n _ H x Hx) as E. cbv beta in E.
  revert E. destruct (rd x) as [v|]; intros E; [discriminate | simpl in E; discriminate E].
Qed.

(* a string s and its NUL at p (fmt_at, pf_arg_asan) *)
Definition oz_eqb (o : option Z) (v : Z) : bool := match o with Some z => z =? v | None => false end.

Lemma snw_str : forall (rd : reader) p s,
  zall 0 (Z.of_nat (length s) + 1) (fun i => oz_eqb (rd (p + i)) (nth (Z.to_nat i) (s ++ [0]) 0)) = true ->
  forall i, 0 <= i <= Z.of_nat (length s) -> rd (p + i) = Some (nth (Z.to_nat i) (s ++ [0]) 0).
Proof.
  intros rd p s H i Hi. pose proof (zall_spec _ _ _ H i ltac:(lia)) as E. cbv beta in E.
  revert E. destruct (rd (p + i)) as [z|]; intros E; cbv beta iota delta [oz_eqb] in E.
  - apply Z.eqb_eq in E. rewrite E. reflexivity.
  - discriminate E.
Qed.

(* the rest of the string's last granule (pf_arg_asan) *)
Lemma snw_slack : forall (rd : reader) w s,
  zall w (str_end w s - w) (fun x => is_someb (rd x)) = true ->
  forall x, w + Z.of_nat (length s) < x < str_end w s -> rd x <> None.
Proof. intros rd w s H x Hx. apply (snw_some rd w (str_end w s - w) H). lia. Qed.

(* the shadow byte of each byte of a range lets that byte be accessed (saddr_ok) *)
Definition sh_okb (rd : reader) (x : Z) : bool :=
  match rd (shadow_of_addr SHADOW_OFF x) with
  | Some s => (s =? 0) || ((x mod 8 <? s) && (s <? 8))
  | None => false
  end.

Lemma snw_ra : forall (rd : reader) a len, zall a len (sh_okb rd) = true -> range_addressable rd SHADOW_OFF a len.
Proof.
  intros rd a len H x Hx. pose proof (zall_spec a len _ H x Hx) as E. unfold sh_okb in E.
  revert E. destruct (rd (shadow_of_addr SHADOW_OFF x)) as [s|]; intros E; cbv beta iota in E; [|discriminate E].
  exists s. split; [reflexivity|]. unfold saddr_ok.
  apply orb_true_iff in E. destruct E as [E|E]; [left; apply Z.eqb_eq; exact E|].
  right. apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.ltb_lt in E1. apply Z.ltb_lt in E2. lia.
Qed.

(* every byte of the range's shadow hull is present *)
Lemma snw_hull : forall (rd : reader) x n,
  zall (shadow_addr x / 8 * 8) (shadow_addr (x + n - 1) / 8 * 8 + 8 - shadow_addr x / 8 * 8)
    (fun s => is_someb (rd s)) = true ->
  shadow_hull_vis rd x n.
Proof. intros rd x n H s Hs. apply (snw_some rd _ _ H). lia. Qed.

(* ==========================================================================
   2. The world and the memories
   ========================================================================== *)

Lemma snw_Hoff : forall segs, H_off_segments segs (fun _ => false).
Proof. intros segs a Ha. cbv beta in Ha. discriminate Ha. Qed.

(* nothing hidden (so the hidden map is constant on every 8-byte word: w_H8), no allocation interval *)
Definition snw_W (segs : list Segment) : world segs :=
  mkW segs (fun _ => false) [] (snw_Hoff segs) (Forall_nil _) (fun _ _ => eq_refl).

(* a byte present in the memory is writable in the world's view of it *)
Lemma snw_writable : forall segs (mem : word -> option byte) lo n a, lo <= a < lo + n ->
  zall lo n (fun x => is_someb (mem (Z_to_bv 64 x))) = true ->
  writable_at segs (mrestrict (w_H (snw_W segs)) mem) a.
Proof.
  intros segs mem lo n a Ha H. pose proof (zall_spec lo n _ H a Ha) as E. cbv beta in E.
  unfold writable_at. rewrite wview_mrestrict_eq by reflexivity.
  unfold wview. revert E. destruct (mem (Z_to_bv 64 a)) as [b|]; intros E.
  - cbv beta iota zeta. discriminate.
  - simpl in E. discriminate E.
Qed.

Definition snw_byte (bs : list Z) (k : Z) : option byte := Some (Z_to_bv 8 (nth (Z.to_nat k) bs 0)).
Definition snw_le8 (v : Z) : list Z := map (fun k => (v / 2 ^ (8 * k)) mod 256) [0; 1; 2; 3; 4; 5; 6; 7].

(* the stack pointer at the call (form_witness.v's CA_SP) and the guard value (musl's second byte 0) *)
Definition SNW_SP : Z := 0x7ffffffde000.
Definition SNW_CVAL : Z := 0x6fb429d13e8c0057.

(* S2: g_names + 8 * 0, "nl%d", i = 0 *)
Definition SNW_F2 : Z := 0x20fa0.
Definition SNW_FMT2 : list Z := [110; 108; 37; 100].
Definition SNW_G_NAMES : Z := 0x62fac0.
Definition SNW_D2 : Z := SNW_G_NAMES.
Definition SNW_T2 : list Z := [110; 108; 48].

(* S1 and S3: "%s" and the name "eth0" *)
Definition SNW_F1 : Z := 0x21680.
Definition SNW_F3 : Z := 0x21240.
Definition SNW_FMT_S : list Z := [37; 115].
Definition SNW_MB : Z := 0x602000000010.       (* mark's block, calloc(1, 0x204) *)
Definition SNW_D1 : Z := SNW_MB + 4.
Definition SNW_BLK : Z := 0x625000000100.      (* LLVMFuzzerTestOneInput's blk, calloc(1, 0x2298) *)
Definition SNW_D3 : Z := SNW_BLK + 0x2094.
Definition SNW_NAME : Z := 0x603000000040.     (* the name's 16-byte buffer *)
Definition SNW_ETH0 : list Z := [101; 116; 104; 48].

(* S2's memory: the guard's .got word, the guard, "nl%d" and its shadow word, g_names and its shadow *)
Definition snw_mem2 : word -> option byte := fun w =>
  let a := bv_unsigned w in
  if inrz a LA_GOT_GUARD 8 then snw_byte (snw_le8 LA_GUARD) (a - LA_GOT_GUARD)
  else if inrz a LA_GUARD 8 then snw_byte (snw_le8 SNW_CVAL) (a - LA_GUARD)
  else if inrz a SNW_F2 5 then snw_byte (SNW_FMT2 ++ [0]) (a - SNW_F2)
  (* 0x7fffc1f0 *)
  else if inrz a (shadow_addr SNW_F2 / 8 * 8) 8 then
    snw_byte [0; 0; 0; 0; 5; 0xf9; 0xf9; 0xf9] (a - shadow_addr SNW_F2 / 8 * 8)
  else if inrz a SNW_G_NAMES 0x200 then Some (Z_to_bv 8 0)
  (* 0x800bdf58 *)
  else if inrz a (shadow_addr SNW_G_NAMES) 0x40 then Some (Z_to_bv 8 0)
  else None.

(* S1's and S3's memory: the guard's .got word, the guard, the two "%s" literals and their shadow words, the two
   calloc blocks and the shadow word of each destination, the name and its shadow word *)
Definition snw_memh : word -> option byte := fun w =>
  let a := bv_unsigned w in
  if inrz a LA_GOT_GUARD 8 then snw_byte (snw_le8 LA_GUARD) (a - LA_GOT_GUARD)
  else if inrz a LA_GUARD 8 then snw_byte (snw_le8 SNW_CVAL) (a - LA_GUARD)
  else if inrz a SNW_F1 3 then snw_byte (SNW_FMT_S ++ [0]) (a - SNW_F1)
  (* 0x7fffc2d0 *)
  else if inrz a (shadow_addr SNW_F1) 8 then
    snw_byte [3; 0xf9; 0xf9; 0xf9; 0; 0; 0; 0] (a - shadow_addr SNW_F1)
  else if inrz a SNW_F3 3 then snw_byte (SNW_FMT_S ++ [0]) (a - SNW_F3)
  (* 0x7fffc248 *)
  else if inrz a (shadow_addr SNW_F3) 8 then
    snw_byte [3; 0xf9; 0xf9; 0xf9; 2; 0xf9; 0xf9; 0xf9] (a - shadow_addr SNW_F3)
  else if inrz a SNW_MB 0x204 then Some (Z_to_bv 8 0)
  (* 0xc047fff8000 *)
  else if inrz a (shadow_addr SNW_MB / 8 * 8) 8 then Some (Z_to_bv 8 0)
  else if inrz a SNW_BLK 0x2298 then Some (Z_to_bv 8 0)
  (* 0xc4a7fff8430 *)
  else if inrz a (shadow_addr SNW_D3 / 8 * 8) 8 then Some (Z_to_bv 8 0)
  else if inrz a SNW_NAME 16 then snw_byte SNW_ETH0 (a - SNW_NAME)
  (* 0xc067fff8008 *)
  else if inrz a (shadow_addr SNW_NAME) 8 then Some (Z_to_bv 8 0)
  else None.

(* ==========================================================================
   3. Tactics
   ========================================================================== *)

Ltac snw_vm := vm_compute; reflexivity.

(* a linear fact over the constants above *)
Ltac snw_num :=
  cbv beta delta [SNW_SP SNW_CVAL SNW_F2 SNW_FMT2 SNW_G_NAMES SNW_D2 SNW_T2 SNW_F1 SNW_F3 SNW_FMT_S SNW_MB SNW_D1
    SNW_BLK SNW_D3 SNW_NAME SNW_ETH0 LINK_SNP_STK ESTACK YG0f.kLowMemEnd YG0f.kHighMemBeg YG0f.kHighMemEnd
    LA_GOT_GUARD LA_GUARD YImgTop.IMG_TOP YImgTop.IMG_LO LINK_FMT_LO LINK_FMT_HI amem_range zdisjoint link_snp_place
    LA_REAL_VFPRINTF LA_REAL_VSNPRINTF LA_ASAN_INITED LA_SHADOW_BASE LA_CHECK_PRINTF LA_REAL_STRNLEN
    LA_INTERCEPT_STRLEN LA_REAL_MEMCHR LA_MEM_LAYOUT LA_COMMON_FLAGS] in *;
  cbn [fst snd length] in *;
  repeat match goal with |- context [2 ^ ?k] => let v := eval vm_compute in (2 ^ k) in change (2 ^ k) with v end;
  lia.

(* a region apart from the window and the destination *)
Ltac snw_disj := unfold snp_out; repeat (apply Forall_cons; [snw_num|]); apply Forall_nil.

(* va_words at xs = [] *)
Ltac snw_va := split; [rewrite app_nil_r; cbn [map]; congruence | intros i Hi; cbn [length] in Hi; lia].

Ltac snw_pieces := repeat (apply Forall_cons; [exact I|]); apply Forall_nil.

Ltac snw_fmt :=
  unfold fmt_at;
  split; [snw_num|];
  split; [apply snw_str; snw_vm|];
  split; [snw_disj|];
  split; [snw_num|];
  split; [apply snw_ra; snw_vm|];
  apply snw_hull; snw_vm.

(* the destination's bytes: writable, outside the window *)
Ltac snw_dest :=
  let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; split; [eapply snw_writable; [exact Ha | snw_vm] | snw_num].

(* the %s argument "eth0" at SNW_NAME; He : str_end SNW_NAME SNW_ETH0 - SNW_NAME = 8 *)
Ltac snw_name He :=
  unfold pf_arg_asan;
  split; [unfold SNW_ETH0; repeat (apply Forall_cons; [cbv beta; lia|]); apply Forall_nil|];
  split; [snw_num|];
  split; [snw_num|];
  split; [apply snw_str; snw_vm|];
  split; [apply snw_slack; snw_vm|];
  split; [rewrite He; snw_disj|];
  split; [snw_num|];
  split; [apply snw_ra; snw_vm|];
  apply snw_hull; snw_vm.

(* FF_link at "%s" with the name *)
Ltac snw_ff_pct He :=
  unfold FF_link; exists SNW_FMT_S, [Ps], [APtr SNW_ETH0];
  split; [snw_fmt|];
  split; [reflexivity|];
  split; [snw_pieces|];
  split; [split; [snw_name He | exact I]|];
  split; [reflexivity|];
  split; [exact I|];
  split; [snw_num|];
  split; [snw_num|];
  split; [split; [rewrite He; snw_num | exact I]|];
  split; [unfold SNW_FMT_S; discriminate|];
  split; [snw_num | exact I].

(* ==========================================================================
   4. The witnesses
   ========================================================================== *)

(* S2 (0x82b14), i = 0: snprintf(g_names, 8, "nl%d", 0) *)
Lemma snw_s2_apre_sat : forall segs (regs : bvmap 5 word),
  getr regs 10 = w64 SNW_D2 -> getr regs 11 = w64 8 -> getr regs 12 = w64 SNW_F2 ->
  argZ regs 3 = 0 -> spZ regs = SNW_SP ->
  asnprintf_link_fpre segs FF_link LINK_SNP_STK (snw_W segs) snw_mem2 regs SNW_D2 8 SNW_F2 []
    (map (argZ regs) [3; 4; 5; 6; 7]) SNW_T2 SNW_CVAL.
Proof.
  intros segs regs Hd Hn Hf Ha3 Hsp.
  assert (Hw : sn_len (8 - 1) SNW_T2 = 4) by (vm_compute; reflexivity).
  unfold asnprintf_link_fpre. rewrite Hw, Hsp.
  change (map (argZ regs) [3; 4; 5; 6; 7]) with (argZ regs 3 :: map (argZ regs) [4; 5; 6; 7]).
  rewrite Ha3.
  split; [exact Hd|]. split; [exact Hn|]. split; [exact Hf|].
  split; [snw_vm|]. split; [snw_vm|].
  split; [snw_va|].
  split; [snw_num|].
  split; [snw_disj|].
  split.
  { unfold FF_link. exists SNW_FMT2, [PLit 110; PLit 108; Pd], [AInt 0].
    split; [snw_fmt|].
    split; [reflexivity|].
    split; [snw_pieces|].
    split; [split; [unfold pf_arg_asan; split; [snw_num | reflexivity] | exact I]|].
    split; [reflexivity|].
    split; [exact I|].
    split; [snw_num|].
    split; [snw_num|].
    split; [exact I|].
    split; [unfold SNW_FMT2; discriminate|].
    exact I. }
  split; [snw_num|]. split; [snw_num|]. split; [snw_num|]. split; [snw_num|].
  split; [snw_dest|].
  split; [snw_num|].
  split; [apply snw_ra; snw_vm|].
  split; [apply snw_hull; snw_vm|].
  split; [snw_num|].
  unfold link_snp_rt_cells. repeat (apply Forall_cons; [snw_num|]). apply Forall_nil.
Qed.

(* S1 (0x89ea8) and S3 (0x839c4), k = 0: snprintf(d, 16, "%s", "eth0") *)
Lemma snw_pct_apre_sat : forall segs (regs : bvmap 5 word) f d,
  (f = SNW_F1 /\ d = SNW_D1) \/ (f = SNW_F3 /\ d = SNW_D3) ->
  getr regs 10 = w64 d -> getr regs 11 = w64 16 -> getr regs 12 = w64 f ->
  argZ regs 3 = SNW_NAME -> spZ regs = SNW_SP ->
  asnprintf_link_fpre segs FF_link LINK_SNP_STK (snw_W segs) snw_memh regs d 16 f []
    (map (argZ regs) [3; 4; 5; 6; 7]) SNW_ETH0 SNW_CVAL.
Proof.
  intros segs regs f d Hs Hd Hn Hf Ha3 Hsp.
  assert (Hw : sn_len (16 - 1) SNW_ETH0 = 5) by (vm_compute; reflexivity).
  assert (He : str_end SNW_NAME SNW_ETH0 - SNW_NAME = 8) by (vm_compute; reflexivity).
  unfold asnprintf_link_fpre. rewrite Hw, Hsp.
  change (map (argZ regs) [3; 4; 5; 6; 7]) with (argZ regs 3 :: map (argZ regs) [4; 5; 6; 7]).
  rewrite Ha3.
  destruct Hs as [[-> ->] | [-> ->]].
  all: split; [exact Hd|].
  all: split; [exact Hn|].
  all: split; [exact Hf|].
  all: split; [snw_vm|].
  all: split; [snw_vm|].
  all: split; [snw_va|].
  all: split; [snw_num|].
  all: split; [snw_disj|].
  all: split; [snw_ff_pct He|].
  all: split; [snw_num|].
  all: split; [snw_num|].
  all: split; [snw_num|].
  all: split; [snw_num|].
  all: split; [snw_dest|].
  all: split; [snw_num|].
  all: split; [apply snw_ra; snw_vm|].
  all: split; [apply snw_hull; snw_vm|].
  all: split; [snw_num|].
  all: apply link_snp_rt_cells_of_place; snw_num.
Qed.

(* S1, remember 0x89ea8: d = mark's block + 4 *)
Lemma snw_s1_apre_sat : forall segs (regs : bvmap 5 word),
  getr regs 10 = w64 SNW_D1 -> getr regs 11 = w64 16 -> getr regs 12 = w64 SNW_F1 ->
  argZ regs 3 = SNW_NAME -> spZ regs = SNW_SP ->
  asnprintf_link_fpre segs FF_link LINK_SNP_STK (snw_W segs) snw_memh regs SNW_D1 16 SNW_F1 []
    (map (argZ regs) [3; 4; 5; 6; 7]) SNW_ETH0 SNW_CVAL.
Proof.
  intros segs regs. exact (snw_pct_apre_sat segs regs SNW_F1 SNW_D1 (or_introl (conj eq_refl eq_refl))).
Qed.

(* S3, LLVMFuzzerTestOneInput 0x839c4: d = blk + 0x2094 *)
Lemma snw_s3_apre_sat : forall segs (regs : bvmap 5 word),
  getr regs 10 = w64 SNW_D3 -> getr regs 11 = w64 16 -> getr regs 12 = w64 SNW_F3 ->
  argZ regs 3 = SNW_NAME -> spZ regs = SNW_SP ->
  asnprintf_link_fpre segs FF_link LINK_SNP_STK (snw_W segs) snw_memh regs SNW_D3 16 SNW_F3 []
    (map (argZ regs) [3; 4; 5; 6; 7]) SNW_ETH0 SNW_CVAL.
Proof.
  intros segs regs. exact (snw_pct_apre_sat segs regs SNW_F3 SNW_D3 (or_intror (conj eq_refl eq_refl))).
Qed.
