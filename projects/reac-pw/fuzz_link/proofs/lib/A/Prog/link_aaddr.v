(* reac-pw/fuzz_link, image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07ca2d80ae9227fa125d40586a02172c96d2b6884f8617ab912061d):
   the addresses of link's own globals and of the entry of each own function. This is the image-A twin of
   section 1 of lib/Prog/link_mem.v: it is the ONE file of the A contracts that holds addresses of this image.
   lib/A/Prog/link_amem.v holds no address; each A contract takes these from here.

   Sources:
   - .symtab of the unstripped twin (sha256 66cd0f159895f119b29a44eb3760cfda78506402a019729057dba69562af9d9f; its
     .text, .rodata and .data are byte-identical to the pin, at the same addresses), read with pyelftools 0.33
     (2026-10-30). ASan pads each instrumented global with a redzone, so a symbol's
     st_size is the object plus its redzone: g_nl is 339968 bytes here, the object is NK_SIZE = 271992.
   - the entries and sizes of the 36 own functions: link-a/facts/asan-set.tsv (internal record, sha256 e26bb6a28c00)
     (the same .symtab).
   - the two .got cells: the listings link-a/listings/{copy_attr,model_read}.fuzz_link.asan.s (internal records, sha256
     cabe69abda9c and 5070c0eed28b) (copy_attr +0x30 `ld a1, 0x56c(a1)` = .got+0x60 = 0xa19d0, value 0xaa438; model_read
     +0x64 `ld a2, 0x59c(a2)` = .got+0xb8 = 0xa1a28, value 0xaa440); 0xaa438 is the symbol
     __asan_shadow_memory_dynamic_address and 0xaa440 the symbol __asan_option_detect_stack_use_after_return. In the kit
     these are as_got_shadow / as_shadow_cell and as_got_uar / as_uar_cell of the image's asyms
     (Reusable/YG0f.v:160-184); AR's const law fixes their contents (YG0f.v:193-195). *)
From Stdlib Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.

(* .bss *)
Definition LA_G_NL : Z := 0x5dcac0.          (* struct nl_kernel g_nl (st_size 339968) *)
Definition LA_G_NAMES : Z := 0x62fac0.       (* char g_names[64][8] (st_size 640) *)
Definition LA_LONG_ALIAS : Z := 0x62fd40.    (* msg_build.long_alias, char[301] (st_size 384) *)
Definition LA_G_SINK : Z := 0x62fec0.        (* FILE *g_sink (st_size 32) *)
Definition LA_G_SAID : Z := 0x62fee0.        (* char g_said[4096] (st_size 5120) *)
Definition LA_G_SAY : Z := 0x6312e0.         (* FILE *g_say, in reac_served_mark.c (st_size 32) *)

(* .data.rel.ro: the two pointer tables *)
Definition LA_ODD : Z := 0xa1760.            (* const char *odd[6] (st_size 96) *)
Definition LA_TEXTS : Z := 0xa17c0.          (* const char *texts[11] (st_size 128) *)

(* .rodata *)
Definition LA_NL_ERRNO_E : Z := 0x21080.     (* nl_errno.e, 6 x int32 (st_size 64) *)

(* .data / .bss of musl (not instrumented: no redzone): stderr's FILE and the open-file list head *)
Definition LA_STDERR_FILE : Z := 0xa5fa0.    (* __stderr_FILE (st_size 232; plain 0x21918) *)
Definition LA_OFL_HEAD : Z := 0x652308.      (* ofl_head (st_size 8; plain 0x95cc8); = ofl_lock 0x652300 + 8 *)

(* The program-global ranges G of the slot's journal (`ajournal_gx G`, lib/A/W_journalG.v): the image bytes one
   call of LLVMFuzzerTestOneInput may change outside its window and its blocks. The ruling (2026-10-30
   12:20Z, the ruling of FORM.md section 10 item 2, on which program-global ranges G holds): the OBJECTS without their ASan redzones (pcap's G_HARNESS
   style, pcap A/Prog/PcapEntryA.v:23), the same objects as the plain frame_G (this unit's
   lib/FrameAPI.v:20-22), each at its image-A address from the twin's .symtab and with its object size:
   __stderr_FILE + 136 (its orientation word, 4 bytes; plain 0x219a0), g_nl (NK_SIZE 271992), g_names (512),
   msg_build.long_alias (301), g_sink (8), g_said (4096), g_say (8), ofl_head (8). Disjoint, in address order. *)
Definition LA_G : list (Z * Z) :=
  [(LA_STDERR_FILE + 136, 4); (LA_G_NL, 271992); (LA_G_NAMES, 512); (LA_LONG_ALIAS, 301);
   (LA_G_SINK, 8); (LA_G_SAID, 4096); (LA_G_SAY, 8); (LA_OFL_HEAD, 8)].
Fixpoint la_sorted (l : list (Z * Z)) : bool :=
  match l with
  | (a, n) :: ((b, _) :: _) as t => (0 <? n) && (a + n <=? b) && la_sorted t
  | _ => true
  end.
Lemma LA_G_sorted : la_sorted LA_G = true. Proof. vm_compute. reflexivity. Qed.

(* .got: the cell holding the shadow base, and the cell holding the side-stack switch *)
Definition LA_GOT_SHADOW : Z := 0xa19d0.     (* .got+0x60, holds LA_SHADOW_CELL *)
Definition LA_SHADOW_CELL : Z := 0xaa438.    (* __asan_shadow_memory_dynamic_address, holds the shadow base *)
Definition LA_GOT_UAR : Z := 0xa1a28.        (* .got+0xb8, holds LA_UAR_CELL *)
Definition LA_UAR_CELL : Z := 0xaa440.       (* __asan_option_detect_stack_use_after_return *)

(* the entry of every own function of image A (link-a/facts/asan-set.tsv (internal record, sha256 e26bb6a28c00)) *)
Definition LA_fuzz_socket : Z := 0x821cc.            (* 196 B *)
Definition LA_fuzz_send : Z := 0x82290.              (* 316 B *)
Definition LA_fuzz_recv : Z := 0x823cc.              (* 688 B *)
Definition LA_fuzz_close : Z := 0x8267c.             (* 80 B *)
Definition LA_fuzz_if_nametoindex : Z := 0x826cc.    (* 264 B *)
Definition LA_LLVMFuzzerTestOneInput : Z := 0x827d4. (* 5468 B *)
Definition LA_kernel : Z := 0x83d30.                 (* 9888 B *)
Definition LA_text_buf : Z := 0x863d0.               (* 92 B *)
Definition LA_model_read : Z := 0x8642c.             (* 776 B *)
Definition LA_check_socket : Z := 0x86734.           (* 80 B *)
Definition LA_index_of : Z := 0x86784.               (* 264 B *)
Definition LA_check_refused : Z := 0x8688c.          (* 32 B *)
Definition LA_check_bounds : Z := 0x868ac.           (* 132 B *)
Definition LA_check_read : Z := 0x86930.             (* 120 B *)
Definition LA_check_requests : Z := 0x869a8.         (* 368 B *)
Definition LA_attr_text : Z := 0x86b18.              (* 820 B *)
Definition LA_nl_error : Z := 0x86e4c.               (* 2032 B *)
Definition LA_talk : Z := 0x8763c.                   (* 1924 B *)
Definition LA_text_of : Z := 0x87dc0.                (* 832 B *)
Definition LA_model_write : Z := 0x88100.            (* 664 B *)
Definition LA_check_write : Z := 0x88398.            (* 60 B *)
Definition LA_mark_quietly : Z := 0x883d4.           (* 124 B *)
Definition LA_check_mark : Z := 0x88450.             (* 60 B *)
Definition LA_check_marks : Z := 0x8848c.            (* 208 B *)
Definition LA_model_decide : Z := 0x8855c.           (* 152 B *)
Definition LA_check_verdict : Z := 0x885f4.          (* 32 B *)
Definition LA_reac_link_alias_read : Z := 0x8867c.   (* 760 B *)
Definition LA_nl_talk : Z := 0x88974.                (* 1504 B *)
Definition LA_reac_link_alias_write : Z := 0x88f54.  (* 1252 B *)
Definition LA_copy_attr : Z := 0x89438.              (* 204 B *)
Definition LA_reac_served_say_to : Z := 0x89504.     (* 12 B *)
Definition LA_reac_served_decide : Z := 0x89510.     (* 152 B *)
Definition LA_reac_served_mark : Z := 0x895a8.       (* 1596 B *)
Definition LA_reac_code_emit : Z := 0x89be4.         (* 464 B *)
Definition LA_remember : Z := 0x89db4.               (* 288 B *)
Definition LA_reac_served_unmark_all : Z := 0x89ed4. (* 1148 B *)

(* the runtime entries copy_attr calls (copy_attr listing +0x58, +0x74): the 4-byte jump to the runtime's strnlen,
   and the checked copy *)
Definition LA_wrapper_strnlen : Z := 0x43048.
Definition LA_checked_memcpy : Z := 0x52d78.
