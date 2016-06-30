/*
 * Copyright (C) 2009 The Android Open Source Project
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

#ifndef _UPDATER_INSTALL_H_
#define _UPDATER_INSTALL_H_

void RegisterInstallFunctions();

//  __attribute__((format(printf, a, b)))这种写法
// __attribute__ format属性可以给被声明的函数加上类似printf或者scanf的特征，它可以使编译器检查函数声明和函数实际调用参数之间的格式化字符串是否匹配。format属性告诉编译器，按照printf, scanf等标准C函数参数格式规则对该函数的参数进行检查
// format的语法格式为：format (archetype, string-index, first-to-check) “archetype”指定是哪种风格；“string-index”指定传入函数的第几个参数是格式化字符串；“first-to-check”指定从函数的第几个参数开始按上述规则进行检查。
// uiPrintf function prints msg to screen as well as logs
void uiPrintf(State* _Nonnull state, const char* _Nonnull format, ...) __attribute__((__format__(printf, 2, 3)));

static int make_parents(char* _Nonnull name);

#endif
