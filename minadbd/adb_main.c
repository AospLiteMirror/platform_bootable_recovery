/*
 * Copyright (C) 2015 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <errno.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>

#define  TRACE_TAG   TRACE_ADB

#include "adb.h"
#include "sysdeps.h"

int adb_main()
{
    //调用exit,在子进程退出时执行adb_cleanup,atexit函数称为终止处理程序注册程序，注册完成以后，当函数终止时exit()函数会主动的调用前面注册的各个函数
    atexit(usb_cleanup);
	//HAVE_FORKEXEC定义在<private/android_filesystem_config.h>中,
	 /*
	* Process creation model.  Choose one:
	*
	* HAVE_FORKEXEC - use fork() and exec()
	* HAVE_WIN32_PROC - use CreateProcess()
	*/

    // No SIGCHLD. Let the service subproc handle its children.
    signal(SIGPIPE, SIG_IGN);

    init_transport_registration();
    // listen on USB
    usb_init();

    D("Event loop starting\n");
    fdevent_loop();

    return 0;
}

